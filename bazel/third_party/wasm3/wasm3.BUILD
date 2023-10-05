# This build file is derived form `CMakeLists.txt` in the `wasm3` repo at
# https://github.com/wasm3/wasm3.
 
cc_binary(
    name = "wasm3",
    srcs = glob(["platforms/app/*.c"]),
    copts = [
        "-std=c99",
        "-Wall",
        "-Wextra",
        "-Wparentheses",
        "-Wundef",
        "-Wpointer-arith",
        "-Wstrict-aliasing=2",
        "-Werror=implicit-function-declaration",
        # Add more compiler flags as needed
    ],
    linkopts = select({
        "//platforms:emscripten_lib": [
            "-s GLOBAL_BASE=1024",
            "-s TOTAL_STACK=2MB",
            "-s INITIAL_MEMORY=4MB",
            "-s ALLOW_MEMORY_GROWTH",
            "-s EXPORTED_FUNCTIONS=\"['_malloc','_free','_main']\"",
        ],
        "//platforms:emscripten": [],
        "//platforms:wasi": ["-Wl,-z,stack-size=8388608"],
        "//platforms:windows": ["-Wl,--stack,8388608"],
        "//platforms:other": [],
    }),
    deps = select({
        "//platforms:wasi": ["@uvwasi//:uvwasi_a", "@uvwasi//:uv_a"],
        "//platforms:other": [],
    }),
)
 
cc_library(
    name = "m3",
    srcs = glob(["source/*.c"]),
    copts = ["-std=c99", "-O3", "-Wfatal-errors", "-fomit-frame-pointer", "-fno-stack-check", "-fno-stack-protector"],
    linkopts = ["-O3"],
)
 
# Add dependencies and configurations specific to each platform