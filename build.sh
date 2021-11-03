#!/bin/sh

(cd packages; sudo dpkg -i *.deb)
(cd kissat; sh build.sh)
(cd cnftools; sh build.sh)
(cd qrat-trim; make)

