#set( LLVM_LINK_COMPONENTS
#  ${LLVM_TARGETS_TO_BUILD}
#  Option
#  Support
#  )

#set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set( SOURCES
	dummy.cpp
    dataFlowAnalysis.h
)

add_clang_executable(genssa
  ssa_main.cpp
  dummy.cpp
  )

#add_clang_executable(cgwpa
#	wpCallGraphBuilder.cpp
#)

target_link_libraries(genssa
  LINK_PRIVATE clangAST
  clangBasic
  clangDriver
  clangFrontend
#  clangRewriteFrontend
#clangStaticAnalyzerFrontend
  clangTooling
  )


#add_custom_target(ast)
#foreach(Sourcefile ${SourceFiles})
#add_custom_command(TARGET ast PRE_BUILD
#       COMMAND clang -emit-ast ${SourceFile} -o /repo/emasabu/spa-test/${SourceFiles}.ast)

install(TARGETS genssa
  RUNTIME DESTINATION bin)
