import Lake
open Lake DSL

package «counterExamples» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CounterExamples» {
  -- add any library configuration options here
}

@[default_target]
lean_lib CRTopology{

}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
