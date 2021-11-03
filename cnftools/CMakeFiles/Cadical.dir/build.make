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

# Utility rule file for Cadical.

# Include the progress variables for this target.
include CMakeFiles/Cadical.dir/progress.make

CMakeFiles/Cadical: CMakeFiles/Cadical-complete


CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-install
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-mkdir
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-download
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-update
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-patch
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-configure
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-build
CMakeFiles/Cadical-complete: cadical/src/Cadical-stamp/Cadical-install
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Completed 'Cadical'"
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles/Cadical-complete
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-done

cadical/src/Cadical-stamp/Cadical-install: cadical/src/Cadical-stamp/Cadical-build
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "No install step for 'Cadical'"
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && /usr/bin/cmake -E echo_append
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && /usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-install

cadical/src/Cadical-stamp/Cadical-mkdir:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Creating directories for 'Cadical'"
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/tmp
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src
	/usr/bin/cmake -E make_directory /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-mkdir

cadical/src/Cadical-stamp/Cadical-download: cadical/src/Cadical-stamp/Cadical-mkdir
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "No download step for 'Cadical'"
	/usr/bin/cmake -E echo_append
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-download

cadical/src/Cadical-stamp/Cadical-update: cadical/src/Cadical-stamp/Cadical-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "No update step for 'Cadical'"
	/usr/bin/cmake -E echo_append
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-update

cadical/src/Cadical-stamp/Cadical-patch: cadical/src/Cadical-stamp/Cadical-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "No patch step for 'Cadical'"
	/usr/bin/cmake -E echo_append
	/usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-patch

cadical/src/Cadical-stamp/Cadical-configure: cadical/tmp/Cadical-cfgcmd.txt
cadical/src/Cadical-stamp/Cadical-configure: cadical/src/Cadical-stamp/Cadical-update
cadical/src/Cadical-stamp/Cadical-configure: cadical/src/Cadical-stamp/Cadical-patch
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Performing configure step for 'Cadical'"
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && ./configure
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && /usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-configure

cadical/src/Cadical-stamp/Cadical-build: cadical/src/Cadical-stamp/Cadical-configure
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Performing build step for 'Cadical'"
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && make -j 8
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical && /usr/bin/cmake -E touch /media/sf_vbox-shared/tmp/new-def-extract/cnftools/cadical/src/Cadical-stamp/Cadical-build

Cadical: CMakeFiles/Cadical
Cadical: CMakeFiles/Cadical-complete
Cadical: cadical/src/Cadical-stamp/Cadical-install
Cadical: cadical/src/Cadical-stamp/Cadical-mkdir
Cadical: cadical/src/Cadical-stamp/Cadical-download
Cadical: cadical/src/Cadical-stamp/Cadical-update
Cadical: cadical/src/Cadical-stamp/Cadical-patch
Cadical: cadical/src/Cadical-stamp/Cadical-configure
Cadical: cadical/src/Cadical-stamp/Cadical-build
Cadical: CMakeFiles/Cadical.dir/build.make

.PHONY : Cadical

# Rule to build all files generated by this target.
CMakeFiles/Cadical.dir/build: Cadical

.PHONY : CMakeFiles/Cadical.dir/build

CMakeFiles/Cadical.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/Cadical.dir/cmake_clean.cmake
.PHONY : CMakeFiles/Cadical.dir/clean

CMakeFiles/Cadical.dir/depend:
	cd /media/sf_vbox-shared/tmp/new-def-extract/cnftools && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools /media/sf_vbox-shared/tmp/new-def-extract/cnftools/CMakeFiles/Cadical.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/Cadical.dir/depend

