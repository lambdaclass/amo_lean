cmake_minimum_required(VERSION 3.16)
project(amolean
    VERSION 0.1.0
    DESCRIPTION "AMO-Lean: Formally verified mathematical optimizations"
    LANGUAGES C
)

# Options
option(AMOLEAN_BUILD_TESTS "Build test programs" ON)
option(AMOLEAN_ENABLE_AVX2 "Enable AVX2 optimizations (x86-64 only)" ON)
option(AMOLEAN_ENABLE_SANITIZERS "Enable ASan/UBSan for testing" OFF)

# Detect architecture and CPU features
include(CheckCCompilerFlag)

set(AMOLEAN_ARCH "unknown")
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64|amd64")
    set(AMOLEAN_ARCH "x86_64")
    message(STATUS "Detected x86-64 architecture")

    # Check for AVX2 support
    if(AMOLEAN_ENABLE_AVX2)
        check_c_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
        if(COMPILER_SUPPORTS_AVX2)
            message(STATUS "AVX2 support enabled")
            set(AMOLEAN_HAS_AVX2 ON)
        else()
            message(WARNING "AVX2 requested but compiler doesn't support -mavx2")
            set(AMOLEAN_HAS_AVX2 OFF)
        endif()
    endif()
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64|ARM64")
    set(AMOLEAN_ARCH "arm64")
    message(STATUS "Detected ARM64 architecture")
    set(AMOLEAN_HAS_AVX2 OFF)
else()
    message(WARNING "Unknown architecture: ${CMAKE_SYSTEM_PROCESSOR}")
    set(AMOLEAN_HAS_AVX2 OFF)
endif()

# Header-only library interface
add_library(amolean INTERFACE)
target_include_directories(amolean INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>
)

# Compile definitions
if(AMOLEAN_HAS_AVX2)
    target_compile_definitions(amolean INTERFACE AMOLEAN_HAS_AVX2=1)
endif()

# Tests
if(AMOLEAN_BUILD_TESTS)
    enable_testing()

    # Compiler flags for tests
    set(TEST_COMPILE_FLAGS -Wall -Wextra -O2)
    if(AMOLEAN_HAS_AVX2)
        list(APPEND TEST_COMPILE_FLAGS -mavx2)
    endif()
    if(AMOLEAN_ENABLE_SANITIZERS)
        list(APPEND TEST_COMPILE_FLAGS -fsanitize=address,undefined)
        set(TEST_LINK_FLAGS -fsanitize=address,undefined)
    endif()

    # Goldilocks field test
    add_executable(test_goldilocks test/test_goldilocks.c)
    target_link_libraries(test_goldilocks PRIVATE amolean)
    target_compile_options(test_goldilocks PRIVATE ${TEST_COMPILE_FLAGS})
    if(AMOLEAN_ENABLE_SANITIZERS)
        target_link_options(test_goldilocks PRIVATE ${TEST_LINK_FLAGS})
    endif()
    add_test(NAME goldilocks_scalar COMMAND test_goldilocks)

    # AVX2 tests (only on x86-64)
    if(AMOLEAN_HAS_AVX2)
        add_executable(test_goldilocks_avx2 test/test_goldilocks_avx2.c)
        target_link_libraries(test_goldilocks_avx2 PRIVATE amolean)
        target_compile_options(test_goldilocks_avx2 PRIVATE ${TEST_COMPILE_FLAGS})
        if(AMOLEAN_ENABLE_SANITIZERS)
            target_link_options(test_goldilocks_avx2 PRIVATE ${TEST_LINK_FLAGS})
        endif()
        add_test(NAME goldilocks_avx2 COMMAND test_goldilocks_avx2)
    endif()
endif()

# Installation
include(GNUInstallDirs)
install(TARGETS amolean EXPORT amoleanTargets)
install(DIRECTORY include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
install(EXPORT amoleanTargets
    FILE amoleanConfig.cmake
    NAMESPACE amolean::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/amolean
)

# Package configuration
include(CMakePackageConfigHelpers)
write_basic_package_version_file(
    "${CMAKE_CURRENT_BINARY_DIR}/amoleanConfigVersion.cmake"
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY SameMajorVersion
)
install(FILES
    "${CMAKE_CURRENT_BINARY_DIR}/amoleanConfigVersion.cmake"
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/amolean
)

# Summary
message(STATUS "")
message(STATUS "AMO-Lean Configuration:")
message(STATUS "  Version:       ${PROJECT_VERSION}")
message(STATUS "  Architecture:  ${AMOLEAN_ARCH}")
message(STATUS "  AVX2:          ${AMOLEAN_HAS_AVX2}")
message(STATUS "  Build tests:   ${AMOLEAN_BUILD_TESTS}")
message(STATUS "  Sanitizers:    ${AMOLEAN_ENABLE_SANITIZERS}")
message(STATUS "")
