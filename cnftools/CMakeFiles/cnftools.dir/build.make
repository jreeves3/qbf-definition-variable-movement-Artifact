# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /media/sf_vbox-shared/tmp/new-def-extract/cnftools

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /media/sf_vbox-shared/tmp/new-def-extract/cnftools

# Include any dependencies generated for this target.
include CMakeFiles/cnftools.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/cnftools.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/cnftools.dir/flags.make

CMakeFiles/cnftools.dir/Main.cc.o: CMakeFiles/cnftools.dir/flags.make
CMakeFiles/cnftools.dir/Main.cc.o: Main.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/cnftools.dir/Main.cc.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/cnftools.dir/Main.cc.o -c /media/sf_vbox-shared/tmp/new-def-extract/cnftools/Main.cc

CMakeFiles/cnftools.dir/Main.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/cnftools.dir/Main.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /media/sf_vbox-shared/tmp/new-def-extract/cnftools/Main.cc > CMakeFiles/cnftools.dir/Main.cc.i

CMakeFiles/cnftools.dir/Main.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/cnftools.dir/Main.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /media/sf_vbox-shared/tmp/new-def-extract/cnftools/Main.cc -o CMakeFiles/cnftools.dir/Main.cc.s

# Object files for target cnftools
cnftools_OBJECTS = \
"CMakeFiles/cnftools.dir/Main.cc.o"

# External object files for target cnftools
cnftools_EXTERNAL_OBJECTS =

cnftools: CMakeFiles/cnftools.dir/Main.cc.o
cnftools: CMakeFiles/cnftools.dir/build.make
cnftools: lib/md5/libmd5.a
cnftools: /usr/lib/x86_64-linux-gnu/libarchive.so
cnftools: cadical/src/Cadical/build/libcadical.a
cnftools: CMakeFiles/cnftools.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable cnftools"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/cnftools.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/cnftools.dir/build: cnftools

.PHONY : CMakeFiles/cnftools.dir/build

CMakeFiles/cnftools.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/cnftools.dir/cmake_clean.cmake
.PHONY : CMakeFiles/cnftools.dir/clean

CMakeFiles/cnftools.dir/depend:
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles/cnftools.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/cnftools.dir/depend
