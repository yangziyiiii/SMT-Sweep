# 🚀 SMT-Sweep
---

## Prerequisites

Before setting up, make sure the following dependencies are installed:

```bash
pip3 install toml
sudo apt install build-essential cmake default-jre libgmp-dev libboost-all-dev libgflags-dev
```

## SETUP

```bash
    ./contrib/setup-glog.sh
    ./contrib/setup-bison.sh
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-smt-switch.sh
    ./configure.sh
    cd build
    make
```

## Usage

For a quick example of how to use the simulator, you may look at **`apps/main_cec.cpp`**
