cmake_minimum_required(VERSION 3.12)
project(pl0)

set(CMAKE_CXX_STANDARD 14)

include_directories(.)

add_executable(pl0
        example.txt
        example2.txt
        example3.txt
        pl0.c
        PL0.h
        set.c
        set.h
        编译原理和技术实践2017.pdf)
