#import "Basic";
#import "Compiler";
#import "String";
#import "File";
#import "Program_Print";
#import "Hash_Table";
Hash  :: #import "Hash";

build :: ()
{
    //  we don't need this file to produce an executable
    //
    set_build_options_dc(.{do_output=false});

    w := compiler_create_workspace("builder");
    options := get_build_options();

    //  get the command-line args
    //
    args := options.compile_time_command_line;

    is_release := false;
    output_path := "build_output/";
    executable_name := "jai_output";  // ".a" will be appended

    for args {
        if "-release" == it {
            is_release = true;
            continue;
        }
        prefix := "-o=";
        if begins_with(it, prefix) {
            path := slice(it, prefix.count, it.count - prefix.count);
            file: string = ---;
            {
                found, dir, file1 := split_from_right(path, #char "/");
                if !found return; // @Incomplete: error report
                output_path = dir;
                file = file1;
            }
            {
                found, name, ext := split_from_right(file, #char ".");
                if !found || "a" != ext return;
                executable_name = name;
            }
            continue;
        }
        //  @Incomplete: unrecognized arguments are currently skipped, throw an error?
    }

    make_directory_if_it_does_not_exist(output_path, true);

    options.output_executable_name = executable_name;
    options.output_path            = output_path;
    options.intermediate_path      = output_path;
    options.output_type            = .STATIC_LIBRARY;

    set_optimization(*options,
        ifx is_release then .VERY_OPTIMIZED
        else .VERY_DEBUG
    );
    set_build_options(options, w);

    //  if our goal is to merely build the files then only `add_build_file`
    //  calls are necessary. but if we want to do stuff at compile time
    //  we start listening for messages, send files to be built, then
    //  handle incoming messages.
    //
    compiler_begin_intercept(w);

    {
        add_build_file("mole.jai", w);
        add_build_file("mule.jai", w);
    }

    //  we are listening to and handling compiler messages in a loop
    //
    message_loop();

    compiler_end_intercept(w);

    post_compilation_check();
}

//  run `build` function when this file is compiled
//  together with do_output=false this makes this file a build script
//
#run build();


refcount_errors := 0;
procedure_headers: [..] *Code_Procedure_Header;
Bitmask :: u64;
Bitmask_full :: 0xffff_ffff_ffff_ffff;
refcount_exceptions: [..] struct {
    header: *Code_Procedure_Header;
    retains_args: Bitmask;
    retains_prod: Bitmask;
};

message_loop :: ()
{
    while true {
        message := compiler_wait_for_message();
        if message.kind == .COMPLETE     break;
        if message.kind != .TYPECHECKED  continue;
        code := cast(*Message_Typechecked) message;
        for code.procedure_headers {
            handle_our_notes(it.expression);
            array_add(*procedure_headers, it.expression);
        }
    }
}

// to test: does the note position matter? in the end vs in the comment?
//
handle_our_notes :: (h: *Code_Procedure_Header)
{
    retains_args: Bitmask;
    retains_prod: Bitmask;
    for h.notes {
        if !begins_with(it.text, "u3") continue;

        if "u3_retains_args" == it.text {
            retains_args = Bitmask_full;
            continue;
        }
        pfix := "u3_retains_arg";
        if begins_with(it.text, pfix) {
            num_str := slice(it.text, pfix.count, it.text.count - pfix.count);
            num, ok := parse_int(*num_str, u64);
            if ok retains_args |= (cast(u64) 1) << num; // @Incomplete: error report
            continue;
        }
        if "u3_retains_prods" == it.text {
            retains_prod = Bitmask_full;
            continue;
        }
        pfix = "u3_retains_prod";
        if begins_with(it.text, pfix) {
            num_str := slice(it.text, pfix.count, it.text.count - pfix.count);
            num, ok := parse_int(*num_str, u64);
            if ok retains_prod |= (cast(u64) 1) << num; // @Incomplete: error report
        }
    }
    if 0 == retains_args && 0 == retains_prod return;
    array_add(*refcount_exceptions, {h, retains_args, retains_prod});
}

post_compilation_check :: ()
{
    for func: procedure_headers {
        // @Incomplete: better heuristic/condition
        is_noun_function: bool = ---;
        {
            using func.enclosing_load.enclosing_import;
            is_noun_function = module_type == .MAIN_PROGRAM
                            || module_type == .FILE && "u3" == module_name;
        }

        if !is_noun_function continue;

        if !func.body_or_null continue;
        retains_args: Bitmask;
        retains_prod: Bitmask;
        // @Incomplete: table
        for exception: refcount_exceptions {
            if exception.header == func {
                retains_args = exception.retains_args;
                retains_prod = exception.retains_prod;
                break;
            }
        }
        check_transfer_semantics(func.body_or_null, retains_args, retains_prod);
    }
}

SpaceKey :: struct {
    name: string;
    shadow: u64;
};

Space :: Table(SpaceKey, s64, space_key_hash, space_key_cmp);

space_clone :: (s: *Space) -> Space
{
    out: Space;
    memcpy(*out, *s, size_of(Space));
    entries_slice_data_size := size_of(Space.Entry) * s.entries.count;
    out.entries.data == alloc(entries_slice_data_size);
    memcpy(out.entries.data, s.entries.data, entries_slice_data_size);

    return out;
}

operator == :: (x: SpaceKey, y: SpaceKey) -> bool
{
    return x.name == y.name && x.shadow == y.shadow;
}

space_key_cmp :: (x: SpaceKey, y: SpaceKey) -> bool
{
    return x == y;
}

space_key_hash :: (k: SpaceKey) -> u32
{
    return Hash.get_hash(k.name) ^ Hash.get_hash(k.shadow);
}

check_transfer_semantics :: (function: *Code_Procedure_Body,
    retains_args: Bitmask,
    retains_prod: Bitmask)
{
    log("%:", function.header.name);

    space: Space;

    for function.header.arguments {
        if !it.type_inst.type_valued_expression continue;
        if .IDENT != it.type_inst.type_valued_expression.kind continue;
        ident := cast(*Code_Ident) it.type_inst.type_valued_expression;
        log("    %: %,", it.name, ident.name);
        table_add(*space, {it.name, 0}, 0);
    }

    transfer_execute_block(*space, function.block.statements);
}

transfer_execute_block :: (s: *Space, block: [] *Code_Node)
{
    for block {
        b: String_Builder;
        print_expression(*b, it);
        res := builder_to_string(*b);
        log("  %    (%)", res, it.kind);
        //
    }
}