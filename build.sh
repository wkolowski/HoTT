#!/bin/sh

# Turn on error propagation.
set -e

cd src && ./build.sh && cd ..

cd notes && ./build.sh && cd ..
