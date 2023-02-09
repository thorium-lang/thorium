#!/usr/bin/env bash
antlr4 -o thorium -Xexact-output-dir -visitor -Dlanguage=Python3 grammar/Thorium.g4
