#import "Basic";
#import "Compiler";
#import "String";
#import "File";

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
    executable_name := "jai_output";

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
                if !found return; // XX error report
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
    }

    make_directory_if_it_does_not_exist(output_path, true);

    options.output_executable_name = executable_name;
    options.output_path            = output_path;
    options.intermediate_path      = output_path;
    options.output_type            = .STATIC_LIBRARY;

    set_optimization(*options,
        ifx is_release then Optimization_Type.VERY_OPTIMIZED
        else Optimization_Type.VERY_DEBUG
    );
    set_build_options(options, w);


    compiler_begin_intercept(w);
    add_build_file("mole.jai", w);
    add_build_file("mule.jai", w);

    //  we are listening to and handling compiler messages in a loop
    //
    message_loop();

    compiler_end_intercept(w);

    noun_transfer_check();
}

//  run `build` function when this file is compiled
//  together with do_output=false this makes this file a build script
//
#run build();


refcount_errors := 0;
procedure_bodies: [..] *Code_Procedure_Body;
refcount_exceptions: [..] struct { name: string; note: string; };

message_loop :: ()
{
    while true {
        message := compiler_wait_for_message();
        if message.kind == .COMPLETE     break;
        if message.kind != .TYPECHECKED  continue;
        code := cast(*Message_Typechecked) message;
        for code.procedure_headers {
            handle_our_notes(it.expression);
        }
        for code.procedure_bodies {
            array_add(*procedure_bodies, it.expression);
        }
    }
}

handle_our_notes :: (h: *Code_Procedure_Header)
{
    // stub
}

noun_transfer_check :: ()
{
    // stub
}