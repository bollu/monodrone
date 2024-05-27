cmake_minimum_required(VERSION 3.15)
project(my_project)

add_subdirectory(third_party/raylib)

# find_package(raylib 3.0 REQUIRED) # Requires at least version 3.0

set(CMAKE_C_STANDARD 11) # Requires C11 standard

add_executable(${PROJECT_NAME} main.c)

target_link_libraries(${PROJECT_NAME} raylib)
target_link_libraries(${PROJECT_NAME} "${CMAKE_SOURCE_DIR}/../.lake/build/lib/libMonodroneFat.a")
# output from leanc --print-ldflags
# -L /Users/bollu/.elan/toolchains/leanprover--lean4---v4.8.0-rc2/lib/lean -lleancpp -lInit -lLean -lleanrt -lc++ -lLake
target_link_directories(${PROJECT_NAME} PUBLIC "/Users/bollu/.elan/toolchains/leanprover--lean4---v4.8.0-rc2/lib/lean")
target_link_libraries(${PROJECT_NAME} leancpp Init Lean leanrt c++ Lake)

# Checks if OSX and links appropriate frameworks (only required on MacOS)
if (APPLE)
    target_link_libraries(${PROJECT_NAME} "-framework IOKit")
    target_link_libraries(${PROJECT_NAME} "-framework Cocoa")
    target_link_libraries(${PROJECT_NAME} "-framework OpenGL")
endif()


