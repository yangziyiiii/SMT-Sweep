#pragma once

#include "smt-switch/generic_sort.h"
#include "smt-switch/smt.h"


namespace wasim
{

    void smt_to_json(const smt::Term & term, const std::string & fname);

    std::string smt_layered_printing(const smt::Term & t);
} // namespace wasim
