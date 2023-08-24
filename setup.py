from setuptools import Extension, setup

setup(
        ext_modules=[
            Extension("repltap.preloadtricks",sources=["src/interpose.c"],extra_compile_args=["-fPIC","-ldl"]),
            Extension("repltap.prng",sources=["src/random.c"],extra_compile_args=["-fPIC","-DMAKE_PUBLIC"])
        ],
        packages=["repltap"]
)
