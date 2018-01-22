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
		path.join(ROOT_DIR, "external/**.hpp"),
		path.join(ROOT_DIR, "external/**.cpp"),
		path.join(ROOT_DIR, "external/**.cc"),
		path.join(ROOT_DIR, "external/gsl/*"),
		path.join(ROOT_DIR, "compat/**.h"),
	}

	configuration { "vs*" }
		files {
			path.join(ROOT_DIR, "debug/**.natvis")
		}

	configuration {}

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
end

function toolProject(_name)
	project (_name)
		kind "ConsoleApp"
		includedirs {
			path.join(ROOT_DIR, "source"),
			path.join(ROOT_DIR, "external"),
			ROOT_DIR,
		}
		files {
			path.join(ROOT_DIR, "tools", _name, "**.cpp"),
			path.join(ROOT_DIR, "tools", _name, "**.h"),
		}
		links {
			"slang"
		}
end

group "tests"
testProject('unittests')

group "tools"
toolProject('depmap')
toolProject('driver')