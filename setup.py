from setuptools import Extension, setup

setup(
        ext_modules=[
            Extension("coqtop.preloadtricks",sources=["src/interpose.c"],extra_compile_args=["-fPIC","-ldl"]),
            Extension("coqtop.prng",sources=["src/random.c"],extra_compile_args=["-fPIC","-DMAKE_PUBLIC"])
        ],
        packages=["coqtop"]
)
