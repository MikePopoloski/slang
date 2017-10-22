--- This is the entry point for the project generation build

solution "slang"
	configurations {
		"Debug",
		"Release",
	}

	platforms {
		"x64"
	}

	language "C++"

local ROOT_DIR = path.getabsolute("..")
local BUILD_DIR = path.join(ROOT_DIR, "build")

dofile "toolchain.lua"
toolchain(BUILD_DIR, BUILD_DIR)

project "slang"
	kind "StaticLib"

	includedirs {
		path.join(ROOT_DIR, "source"),
		path.join(ROOT_DIR, "external"),
		ROOT_DIR,
	}

	files {
		path.join(ROOT_DIR, "source/**.h"),
		path.join(ROOT_DIR, "source/**.cpp"),
		path.join(ROOT_DIR, "external/**.h"),
		path.join(ROOT_DIR, "external/**.cpp"),
		path.join(ROOT_DIR, "external/**.cc"),
		path.join(ROOT_DIR, "external/gsl/*"),
		path.join(ROOT_DIR, "compat/**.h"),
	}

	configuration { "vs*" }
		buildoptions {
			"/FI prelude.h"
		}

	configuration { "linux-gcc* or linux-clang*" }
		buildoptions {
			"-include prelude.h"
		}

function testProject(_name)
	project (_name)
		kind "ConsoleApp"
		includedirs {
			path.join(ROOT_DIR, "source"),
			path.join(ROOT_DIR, "external"),
			ROOT_DIR,
		}
		files {
			path.join(ROOT_DIR, "tests", _name, "**.cpp"),
			path.join(ROOT_DIR, "tests", _name, "**.h"),
		}
		links {
			"slang"
		}

	configuration { "vs*" }
		buildoptions {
			"/FI prelude.h"
		}

	configuration { "linux-gcc* or linux-clang*" }
		buildoptions {
			"-include prelude.h"
		}
end

group "tests"
testProject('unittests')
testProject('paramrewriter')
testProject('depmap')