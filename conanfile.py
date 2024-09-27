from conan import ConanFile
from conan.tools.cmake import cmake_layout


class CompressorRecipe(ConanFile):
    settings = "os", "compiler", "build_type", "arch"
    generators = "CMakeToolchain", "CMakeDeps"

    def requirements(self):
        self.requires("mimalloc/2.1.7")
        self.requires("catch2/3.7.1")
        self.requires("pybind11/2.13.6")
        self.requires("fmt/11.0.2")

    def layout(self):
        self.folders.build_folder_vars = [
            "settings.compiler",
            "settings.arch",
            "options.shared",
        ]
        cmake_layout(self)
