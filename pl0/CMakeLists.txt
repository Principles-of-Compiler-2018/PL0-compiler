cmake_minimum_required(VERSION 3.12)
project(pl0)

set(CMAKE_CXX_STANDARD 14)

include_directories(.)

add_executable(pl0
        Debug/example.txt
        Debug/plcc
        pl0.out.dSYM/Contents/Resources/DWARF/pl0.out
        pl0.out.dSYM/Contents/Info.plist
        CMakeLists.txt
        example0.txt
        example2.txt
        example3.txt
        pl0.c
        PL0.h
        pl0.out
        set.c
        set.h
        编译原理和技术实践2017.pdf)
