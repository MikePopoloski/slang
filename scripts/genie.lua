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
		path.join(ROOT_DIR, "include"),
		path.join(ROOT_DIR, "external"),
	}

	files {
		path.join(ROOT_DIR, "include/**.h"),
		path.join(ROOT_DIR, "source/**.h"),
		path.join(ROOT_DIR, "source/**.cpp"),
		path.join(ROOT_DIR, "external/**.h"),
		path.join(ROOT_DIR, "external/**.cpp"),
		path.join(ROOT_DIR, "external/**.cc"),
	}

group "tests"

project "unittests"
	kind "ConsoleApp"
	includedirs {
		path.join(ROOT_DIR, "include"),
		path.join(ROOT_DIR, "external"),
	}
	files {
		path.join(ROOT_DIR, "tests/unit_tests/**.cpp")
	}
	links {
		"slang"
	}

	configuration { "vs*" }
		buildoptions {
			"/Fdunittests_compiler.pdb"
		}

	configuration {}

project "filetests"
	kind "ConsoleApp"
	includedirs {
		path.join(ROOT_DIR, "include"),
		path.join(ROOT_DIR, "external"),
	}
	files {
		path.join(ROOT_DIR, "tests/file_tests/**.cpp")
	}
	links {
		"slang"
	}

	configuration { "vs*" }
		buildoptions {
			"/Fdfiletests_compiler.pdb"
		}

	configuration {}