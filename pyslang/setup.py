from subprocess import check_output

from skbuild import setup


def get_git_version():
    command = "git describe --tags --long --dirty"
    fmt = "{tag}+{commitcount}.{gitsha}"

    try:
        git_version = check_output(command.split()).decode("utf-8").strip()
    except Exception:
        return None

    if git_version.startswith("v"):
        git_version = git_version[1:]

    parts = git_version.split("-")
    assert len(parts) in (3, 4)
    dirty = len(parts) == 4
    tag, count, sha = parts[:3]
    if count == "0" and not dirty:
        version = tag
    else:
        version = fmt.format(tag=tag, commitcount=count, gitsha=sha)
        if dirty:
            version = version + ".dirty"

    return version


def get_version():
    # Try to read existing release version file.
    try:
        f = open("RELEASE-VERSION", "r")
        fs_version = f.readlines()[0].strip()
    except Exception:
        fs_version = None

    # Get the version as described by git, if present.
    version = get_git_version()
    if version is None:
        version = fs_version

    if version is None:
        raise ValueError("Cannot find the version number!")

    if version != fs_version:
        f = open("RELEASE-VERSION", "w")
        f.write("{}\n".format(version))

    return version


setup(
    version=get_version(),
    packages=[""],
    package_dir={"": "source"},
    cmake_source_dir="../",
    cmake_install_dir="source",
    cmake_install_target="pyslang-install-pylib",
    cmake_args=[
        "-DSLANG_INCLUDE_TESTS=OFF",
        "-DSLANG_INCLUDE_TOOLS=OFF",
        "-DSLANG_INCLUDE_PYLIB=ON",
    ],
    include_package_data=True,
    extras_require={"test": ["pytest"]},
)
