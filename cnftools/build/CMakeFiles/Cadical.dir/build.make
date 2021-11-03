# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.17

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Disable VCS-based implicit rules.
% : %,v


# Disable VCS-based implicit rules.
% : RCS/%


# Disable VCS-based implicit rules.
% : RCS/%,v


# Disable VCS-based implicit rules.
% : SCCS/s.%


# Disable VCS-based implicit rules.
% : s.%


.SUFFIXES: .hpux_make_needs_suffix_list


# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

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
CMAKE_COMMAND = /usr/local/bin/cmake

# The command to remove a file.
RM = /usr/local/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /root/cnftools

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /root/cnftools/build

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
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Completed 'Cadical'"
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/CMakeFiles
	/usr/local/bin/cmake -E touch /root/cnftools/build/CMakeFiles/Cadical-complete
	/usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-done

cadical/src/Cadical-stamp/Cadical-install: cadical/src/Cadical-stamp/Cadical-build
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "No install step for 'Cadical'"
	cd /root/cnftools/build/cadical/src/Cadical && /usr/local/bin/cmake -E echo_append
	cd /root/cnftools/build/cadical/src/Cadical && /usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-install

cadical/src/Cadical-stamp/Cadical-mkdir:
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Creating directories for 'Cadical'"
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/src/Cadical
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/src/Cadical
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/tmp
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/src/Cadical-stamp
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/src
	/usr/local/bin/cmake -E make_directory /root/cnftools/build/cadical/src/Cadical-stamp
	/usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-mkdir

cadical/src/Cadical-stamp/Cadical-download: cadical/src/Cadical-stamp/Cadical-gitinfo.txt
cadical/src/Cadical-stamp/Cadical-download: cadical/src/Cadical-stamp/Cadical-mkdir
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Performing download step (git clone) for 'Cadical'"
	cd /root/cnftools/build/cadical/src && /usr/local/bin/cmake -P /root/cnftools/build/cadical/tmp/Cadical-gitclone.cmake
	cd /root/cnftools/build/cadical/src && /usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-download

cadical/src/Cadical-stamp/Cadical-update: cadical/src/Cadical-stamp/Cadical-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Performing update step for 'Cadical'"
	cd /root/cnftools/build/cadical/src/Cadical && /usr/local/bin/cmake -P /root/cnftools/build/cadical/tmp/Cadical-gitupdate.cmake

cadical/src/Cadical-stamp/Cadical-patch: cadical/src/Cadical-stamp/Cadical-download
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "No patch step for 'Cadical'"
	/usr/local/bin/cmake -E echo_append
	/usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-patch

cadical/src/Cadical-stamp/Cadical-configure: cadical/tmp/Cadical-cfgcmd.txt
cadical/src/Cadical-stamp/Cadical-configure: cadical/src/Cadical-stamp/Cadical-update
cadical/src/Cadical-stamp/Cadical-configure: cadical/src/Cadical-stamp/Cadical-patch
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Performing configure step for 'Cadical'"
	cd /root/cnftools/build/cadical/src/Cadical && ./configure
	cd /root/cnftools/build/cadical/src/Cadical && /usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-configure

cadical/src/Cadical-stamp/Cadical-build: cadical/src/Cadical-stamp/Cadical-configure
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --blue --bold --progress-dir=/root/cnftools/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Performing build step for 'Cadical'"
	cd /root/cnftools/build/cadical/src/Cadical && make -j 8
	cd /root/cnftools/build/cadical/src/Cadical && /usr/local/bin/cmake -E touch /root/cnftools/build/cadical/src/Cadical-stamp/Cadical-build

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
	cd /root/cnftools/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /root/cnftools /root/cnftools /root/cnftools/build /root/cnftools/build /root/cnftools/build/CMakeFiles/Cadical.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/Cadical.dir/depend

