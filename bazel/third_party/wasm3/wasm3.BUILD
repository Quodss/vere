# This build file is derived form `CMakeLists.txt` in the `wasm3` repo at
# https://github.com/wasm3/wasm3.
 
cc_library(
    name = "wasm3",
    srcs = glob(["source/*.c"]),
    hdrs = glob(["source/wasm3.h", "source/*.h"]),
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
    visibility = ["//visibility:public"],
)

cc_library(
    name = "m3_lib",
    srcs = glob(["source/*.c"]),
    hdrs = glob(["source/wasm3.h", "source/*.h"]),
    copts = ["-std=c99", "-O3", "-Wfatal-errors", "-fomit-frame-pointer", "-fno-stack-check", "-fno-stack-protector"],
    linkopts = ["-O3"],
    visibility = ["//visibility:public"],
)
