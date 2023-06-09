from conan import ConanFile
from conan.tools.cmake import cmake_layout

WITHOUT_BOOST = (
    "atomic",
    "chrono",
    "context",
    "contract",
    "coroutine",
    "date_time",
    "exception",
    "fiber",
    "filesystem",
    "graph",
    "graph_parallel",
    "iostreams",
    "json",
    "locale",
    "log",
    "math",
    "mpi",
    "nowide",
    "program_options",
    "python",
    "random",
    "regex",
    "serialization",
    "stacktrace",
    "test",
    "thread",
    "timer",
    "type_erasure",
    "url",
    "wave",
)


class CompressorRecipe(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeToolchain", "CMakeDeps"

    def configure(self):
        boostopts = self.options["boost/*"]
        boostopts.zlib = False
        boostopts.bzip2 = False
        for _name in WITHOUT_BOOST:
            setattr(boostopts, f"without_{_name}", True)

    def requirements(self):
        self.requires("mimalloc/2.1.2")
        self.requires("catch2/3.3.2")
        self.requires("pybind11/2.10.4")
        self.requires("fmt/10.0.0")
        self.requires("boost/1.82.0")

    def layout(self):
        self.folders.build_folder_vars = [
            "settings.compiler",
            "settings.arch",
            "options.shared",
        ]
        cmake_layout(self)
