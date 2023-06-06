from setuptools import Extension, setup

setup(
        ext_modules=[
            Extension("repltap.preloadtricks",sources=["src/interpose.c"],extra_compile_args=["-fPIC","-ldl"])
        ],
        packages=["repltap"]
)
