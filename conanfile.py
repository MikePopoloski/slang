from conan import ConanFile
from conan.tools.cmake import cmake_layout


class CompressorRecipe(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeToolchain", "CMakeDeps"

    def requirements(self):
        self.requires("mimalloc/2.1.2")
        self.requires("catch2/3.3.2")
        self.requires("pybind11/2.10.4")
        self.requires("fmt/10.0.0")

    def layout(self):
        self.folders.build_folder_vars = [
            "settings.compiler",
            "settings.arch",
            "options.shared",
        ]
        cmake_layout(self)
