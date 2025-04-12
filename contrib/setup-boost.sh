#!/bin/bash

set -e  # Exit on error

BOOST_VERSION=1.81.0
BOOST_VERSION_UNDERSCORE=${BOOST_VERSION//\./_}
BOOST_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )/../deps/boost"

if [ -d "${BOOST_DIR}" ]; then
    echo "Boost directory already exists. Skipping setup."
    exit 0
fi

mkdir -p ${BOOST_DIR}
cd ${BOOST_DIR}

echo "Downloading Boost ${BOOST_VERSION}..."
BOOST_URL="https://sourceforge.net/projects/boost/files/boost/${BOOST_VERSION}/boost_${BOOST_VERSION_UNDERSCORE}.tar.gz"
wget --no-check-certificate ${BOOST_URL} || {
    echo "Failed to download from SourceForge, trying alternative source..."
    BOOST_URL="https://boostorg.jfrog.io/artifactory/main/release/${BOOST_VERSION}/source/boost_${BOOST_VERSION_UNDERSCORE}.tar.gz"
    wget --no-check-certificate ${BOOST_URL}
}

echo "Extracting Boost..."
tar xzf boost_${BOOST_VERSION_UNDERSCORE}.tar.gz || {
    echo "Failed to extract Boost"
    exit 1
}

cd boost_${BOOST_VERSION_UNDERSCORE}

echo "Building Boost..."
./bootstrap.sh --with-libraries=system,filesystem,program_options,thread || {
    echo "Failed to bootstrap Boost"
    exit 1
}

./b2 install --prefix=${BOOST_DIR}/install link=static threading=multi || {
    echo "Failed to build Boost"
    exit 1
}

echo "Boost installation completed successfully!"