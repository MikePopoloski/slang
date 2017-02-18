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
	}

	files {
		path.join(ROOT_DIR, "source/**.h"),
		path.join(ROOT_DIR, "source/**.cpp"),
		path.join(ROOT_DIR, "external/**.h"),
		path.join(ROOT_DIR, "external/**.cpp"),
		path.join(ROOT_DIR, "external/**.cc"),
	}

function testProject(_name)
	project (_name)
		kind "ConsoleApp"
		includedirs {
			path.join(ROOT_DIR, "source"),
			path.join(ROOT_DIR, "external"),
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
				"/Fd" .. _name .. "_compiler.pdb"
			}

		configuration {}
end

group "tests"
testProject('unittests')
testProject('filetests')
testProject('paramrewriter')