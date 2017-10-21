function toolchain(_buildDir, _libDir)

	newoption {
		trigger = "gcc",
		value = "GCC",
		description = "Choose GCC flavor",
		allowed = {
			{ "linux-gcc",       "Linux (GCC compiler)"       },
			{ "linux-clang",     "Linux (Clang compiler)"     },
		},
	}

	newoption {
		trigger = "xcode",
		value = "xcode_target",
		description = "Choose XCode target",
		allowed = {
			{ "osx", "OSX" },
		}
	}

	newoption {
		trigger     = "with-dynamic-runtime",
		description = "Dynamically link with the runtime rather than statically",
	}

	newoption {
		trigger     = "with-32bit-compiler",
		description = "Use 32-bit compiler instead 64-bit.",
	}

	newoption {
		trigger     = "with-avx",
		description = "Use AVX extension.",
	}

	newoption {
		trigger     = "with-coverage",
		description = "Compile with code coverage support",
	}

	-- Avoid error when invoking genie --help.
	if (_ACTION == nil) then return false end

	location (path.join(_buildDir, "projects", _ACTION))

	if _ACTION == "clean" then
		os.rmdir(_buildDir)
		os.mkdir(_buildDir)
		os.exit(1)
	end

	local windowsPlatform = "10.0.15063.0"
	local compiler32bit = false
	if _OPTIONS["with-32bit-compiler"] then
		compiler32bit = true
	end

	if _ACTION == "gmake" or _ACTION == "ninja" then

		if nil == _OPTIONS["gcc"] then
			print("GCC flavor must be specified!")
			os.exit(1)
		end

		if "linux-gcc" == _OPTIONS["gcc"] then

			if os.is("macosx") then
				premake.gcc.cc  = "gcc-7"
				premake.gcc.cxx = "g++-7"
			else
				premake.gcc.cc  = "gcc"
				premake.gcc.cxx = "g++"
			end

			premake.gcc.ar  = "ar"
			location (path.join(_buildDir, "projects", _ACTION .. "-linux"))

		elseif "linux-clang" == _OPTIONS["gcc"] then
			premake.gcc.cc  = "clang"
			premake.gcc.cxx = "clang++"
			premake.gcc.ar  = "ar"
			location (path.join(_buildDir, "projects", _ACTION .. "-linux-clang"))

		end

	elseif _ACTION == "xcode4" then

		if "osx" == _OPTIONS["xcode"] then
			premake.xcode.toolset = "macosx"
			location (path.join(_buildDir, "projects", _ACTION .. "-osx"))
		end

	elseif _ACTION == "vs2017" then

		local action = premake.action.current()
		action.vstudio.windowsTargetPlatformVersion = windowsPlatform
		action.vstudio.windowsTargetPlatformMinVersion = windowsPlatform

	end

	if not _OPTIONS["with-dynamic-runtime"] then
		flags { "StaticRuntime" }
	end

	if _OPTIONS["with-avx"] then
		flags { "EnableAVX" }
	end

	flags {
		"NoPCH",
		"NativeWChar",
		"NoEditAndContinue",
		"Symbols",
		"ExtraWarnings"
	}

	defines {
		"__STDC_LIMIT_MACROS",
		"__STDC_FORMAT_MACROS",
		"__STDC_CONSTANT_MACROS",
	}

	configuration { "Debug" }
		targetsuffix "Debug"
		defines {
			"_DEBUG",
		}

	configuration { "Release" }
		flags {
			"NoBufferSecurityCheck",
			"NoFramePointer",
			"OptimizeSpeed",
		}
		defines {
			"NDEBUG",
		}
		targetsuffix "Release"

	configuration { "vs*" }
		defines {
			"WIN32",
			"_WIN32",
			"_UNICODE",
			"UNICODE",
			"_SCL_SECURE=0",
			"_SECURE_SCL=0",
			"_SCL_SECURE_NO_WARNINGS",
			"_CRT_SECURE_NO_WARNINGS",
			"_CRT_SECURE_NO_DEPRECATE",
		}
		buildoptions {
			"/wd4324", -- warning C4324: '': structure was padded due to alignment specifier
			"/std:c++latest",
			"/permissive-"
		}
		linkoptions {
			"/ignore:4221", -- LNK4221: This object file does not define any previously undefined public symbols, so it will not be used by any link operation that consumes this library
		}

	configuration { "x64", "vs*" }
		defines { "_WIN64" }
		targetdir (path.join(_buildDir, "win64_" .. _ACTION, "bin"))
		objdir (path.join(_buildDir, "win64_" .. _ACTION, "obj"))
		libdirs {
			path.join(_libDir, "lib/win64_" .. _ACTION),
		}

	configuration { "x64", "vs2017" }
		defines { "_WIN64" }
		targetdir (path.join(_buildDir, "win64_" .. _ACTION, "bin"))
		objdir (path.join(_buildDir, "win64_" .. _ACTION, "obj"))
		libdirs {
			path.join(_libDir, "lib/win64_" .. _ACTION),
		}

	configuration { "linux-gcc" }
		buildoptions {
			"-mfpmath=sse",
		}

	if _OPTIONS["with-coverage"] then
		configuration { "linux-gcc" }
			buildoptions {
				"--coverage",
				"-fno-inline",
				"-fno-inline-small-functions",
				"-fno-default-inline",
				"-fno-omit-frame-pointer",
				"-fno-optimize-sibling-calls"
			}
			linkoptions {
				"--coverage"
			}
	else
		configuration { "linux-gcc* or linux-clang*" }
			linkoptions {
				"-Wl,--gc-sections",
				"-Wl,--as-needed",
			}
	end

	configuration { "linux-gcc* or linux-clang*" }
		buildoptions {
			"-msse2",
			"-Wunused-value",
			"-Wformat=2",
			"-Wnull-dereference",
			"-Wimplicit-fallthrough=5",
--			"-Wsuggest-override",
			"-Walloc-zero",
--			"-Wshadow",
--			"-Wconversion",
			"-Wlogical-op",
			"-Wlogical-not-parentheses",
			"-Wvla",
			"-Wnoexcept",
--			"-Wnon-virtual-dtor"
		}
		buildoptions_cpp {
			"-std=c++1z",
		}
		if os.is("macosx") then
			links {
				"dl",
			}
			linkoptions {
				"-W",
			}
		else
			links {
				"rt",
				"dl",
			}
		end

	configuration { "linux-gcc* or linux-clang*", "Debug" }
		buildoptions {
			"-g"
		}

	configuration { "linux-gcc*", "x64" }
		targetdir (path.join(_buildDir, "linux64_gcc/bin"))
		objdir (path.join(_buildDir, "linux64_gcc/obj"))
		libdirs { path.join(_libDir, "lib/linux64_gcc") }
		buildoptions {
			"-m64",
		}

	configuration { "linux-clang*", "x64" }
		targetdir (path.join(_buildDir, "linux64_clang/bin"))
		objdir (path.join(_buildDir, "linux64_clang/obj"))
		libdirs { path.join(_libDir, "lib/linux64_clang") }
		buildoptions {
			"-m64",
		}

	configuration { "osx", "x64" }
		targetdir (path.join(_buildDir, "osx64_clang/bin"))
		objdir (path.join(_buildDir, "osx64_clang/obj"))
		buildoptions {
			"-m64",
		}

	configuration { "osx" }
		buildoptions_cpp {
			"-std=c++11",
		}
		buildoptions {
			"-Wfatal-errors",
			"-msse2",
			"-Wunused-value",
			"-Wundef",
		}

	configuration {} -- reset configuration

	return true
end
