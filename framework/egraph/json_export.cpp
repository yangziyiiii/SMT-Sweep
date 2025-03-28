#include "framework/egraph/json_export.h"

#include "json/json.hpp"

#include <iostream>
#include <fstream>

namespace wasim
{

void smt_to_json(const smt::Term & term, const std::string & fname) {
  using namespace nlohmann;
  json ret;
  /* 
    "id": integer,
    "op":"",
    "opidx1" : ,  integer/null
    "opidx2" : ,  integer/null
    "width": ,
    "children": ,
  */

  std::vector<std::pair<smt::Term, bool>> to_visit({ { term, false } });

  unsigned num_id = 0;
  std::unordered_map<smt::Term, unsigned>  term_id_map;
  std::unordered_set<std::string> opstr_set;

  
  while (to_visit.size()) {
    auto & t = to_visit.back();
    if (term_id_map.find(t.first) != term_id_map.end()) {
      to_visit.pop_back();
      continue;
    }

    if (t.second) { // have visited its children
      // record it
      auto id = num_id++;
      term_id_map.emplace(t.first, id);

      smt::Op op = t.first->get_op();
      auto op_str = smt::to_string(op.prim_op);
      if (t.first->is_value())
        op_str = "constant";
      else if (t.first->is_symbol() || t.first->is_symbolic_const())
        op_str = "variable";

      if (opstr_set.find(op_str) == opstr_set.end())
        opstr_set.emplace(op_str);

      ret[std::to_string(id)] = json::object();

      auto & jiterm = ret[std::to_string(id)] ;

      jiterm["id"] = id;
      jiterm["op"] = op_str;
      if (op_str == "constant" || op_str == "variable") 
        jiterm["value"] = t.first->to_string();

      if(op.num_idx)
        jiterm["opidx0"] = op.idx0;
      else
        jiterm["opidx0"] = nullptr;      

      if (op.num_idx > 1)
        jiterm["opidx1"] = op.idx1;
      else
        jiterm["opidx1"] = nullptr;
      
      auto sort = t.first->get_sort();
      if ( sort->get_sort_kind() == smt::SortKind::BOOL ) {
        jiterm["width"] = 1; // Or maybe 0 ?
      } else if (sort->get_sort_kind() == smt::SortKind::BV) {
        jiterm["width"] = sort->get_width();
      } else {
        jiterm["width"] = -1; // unrecognized;
      }

      std::vector<unsigned> children;
      for (const auto & tt : *(t.first)) {
        children.push_back( term_id_map.at(tt) );
      }
      jiterm["children"] = children;

      to_visit.pop_back();
    } 
    else { // have not visited its children
      for (const auto & tt : *(t.first)) {
        to_visit.push_back(std::make_pair(tt,false));
      }
      t.second = true;
    }
  } // end of while
  
  ret["allops"] = opstr_set;
  ret["root"] = term_id_map.at(term);

  std::ofstream fout(fname);
  fout << std::setw(4) << ret << std::endl;
} // end of smt_to_json


static void layered_visit(const smt::Term & term, const std::string & identation, std::string & strout) {
  
  if(term->is_symbol() || term->is_symbolic_const() || term->is_value()) {
    strout += identation + term->to_string() + "\n";
    return;
  }
  strout += identation + term->get_op().to_string() + "\n";
  for (const auto & tt : *term) {
    layered_visit(tt, identation + "\t", strout);
  }
}

std::string smt_layered_printing(const smt::Term & term) {
  // DFS of t
  std::string ret;
  layered_visit(term, "", ret);
  return ret;
}


} // namespace wasim
