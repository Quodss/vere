#import "Basic";
#import "Compiler";
#import "String";
#import "File";

build :: () {
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
        if 0 == compare(it, "-release") {
            is_release = true;
            continue;
        }
        prefix := "-o=";
        if begins_with(it, prefix) {
            path := slice(it, prefix.count, it.count - prefix.count);
            found, dir, file := split_from_right(path, #char "/");
            if !found return; // XX error report
            output_path = dir;

            name, ext: string;
            found, name, ext = split_from_right(file, #char ".");
            if !found return;
            if 0 != compare(ext, "a") return;
            executable_name = name;
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

    add_build_file("mole.jai", w);
    add_build_file("mule.jai", w);
}

//  run `build` function when this file is compiled
//  together with do_output=false this makes this file a build script
//
#run build();