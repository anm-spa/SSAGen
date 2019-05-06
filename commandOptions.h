#ifndef LLVM_CLANG_COMMANDOPTIONS_H
#define LLVM_CLANG_COMMANDOPTIONS_H

#include "clang/Tooling/CommonOptionsParser.h"

static cl::OptionCategory MainCat("Perform static analysis");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("\nMore help text...");

enum DLevel {
    O, O1, O2, O3
};
cl::opt<DLevel> DL("dl", cl::desc("Choose Debug level:"),
                           cl::values(
                                      clEnumValN(O, "none", "No debugging"),
                                      clEnumVal(O1, "Minimal debug info"),
                                      clEnumVal(O2, "Expected debug info"),
                                      clEnumVal(O3, "Extended debug info")), cl::cat(MainCat));


#endif
