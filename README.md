# Stripper
Stripper is a command-line utility that allows you to transform PDDL files using certain features into plain STRIPS-based PDDL files, for compatibility.

For example, if you have a planning system that only supports STRIPS planning, you can still test it on problems that were not created around the years 1990-2000. Stripper uses behind the scenes `pddl`, a PDDL 3.1 parser for Python and so at a most basic level cannot work on your files if they use features the parser still doesn't support (of which currently there are a few). Furthermore, Stripper doesn't support lowering to STRIPS from all the requirements the PDDL parser supports. Rather, Stripper only supports the following requirements:

- `:strips` (Obviously)
- `:typing`
- `:negative-preconditions`
- `:equality`
- Constants (This isn't a requirement, but still some PDDL systems do not support these)

Once Stripper finishes simplifying a file, it will also remove all of the relevant requirements from it, so that the file may be used with the relevant tools.

It should be noted that the CLI of Stripper doesn't work with domain-problem pairs, partially because this is very tedious to work with, partially because sometimes a domain will sometimes have multiple problems, and finally partially because Stripper shouldn't be run on a file multiple times (because once it finishes running on a domain file, it generates metadata that it then uses to work on problem files).

Instead Stripper simply accepts a directory and simplifies all of the files in that directory, making sure to match the right problem to the right domainm using the data in the files (making working with pairs again unneccessary).

### NOTE:
Stripper has a particular focus on correctness - not readability, or prettyness. Files generated should be machine readable and under the assumption the provided domains and problems are perfectly valid, never be erroneous. This means that the resulting files can sometimes look awkward, with names such as `truck_______`. This for example is done to make sure the name is actually unique and doesn't interefere with another name in the file.

## Requirements
Stripper requires several modern Python features, such as pattern matching, and type hints. It was been successfully tested on Python 3.11.4, however your mileage may very. To use it, one must install `pddl`, `click` and `tqdm`.

## CLI
To invoke Stripper, simply run the python script like so:
```
python __main__.py <DIRECTORY>
```
Or alternatively run the script using the directory containing `__main__.py`, like:
```
python stripper <DIRECTORY>
```
Stripper will then go over all `.pddl` files in the directory recursively and change them in-place.

# Contributing
Feel free to add support for new features, or to expand the CLI, by opening a pull request, or of course to open an issue. Note however that this tool is mainly used for powering research I am doing and so I will likely not be adding new features to it myself, unless I will actively require them.
