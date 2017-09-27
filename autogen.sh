#!/bin/bash
# ======================================
# Definitions
# ======================================
function fail {
    echo "$1\b"
    exit 100
}
# ======================================
# Autogen script
# ======================================
# First initint submodules
echo "Initializing submodules..."
echo " > > > > minisat..."
git submodule init minisat || fail "Failed to init minisat submodule!"
echo " o o o o updating..."
git submodule update minisat  || fail "Failed to patch minisat submodule!"
# Patching minisat
echo "Patching minisat..."
cd minisat
for patch in ../patch/*
do
    echo " > > > > applying $patch..."
    git apply "$patch" || fail "Error while applying $patch to minisat!"
done
cd ..
echo "minisat patched!"
# Constructing build directory
echo "Initializing build directory..."
mkdir build
# Pre building
cd build  || fail "Failed to enter build directory"
echo "Configuring framework..."
cmake .. || fail "Could not configure build!"
echo "Building framework..."
make || fail "Framework build failed!"
echo "Checking framework..."
make test || fail "Framework tests failed!"
cd ..
