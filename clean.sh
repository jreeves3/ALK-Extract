#!/bin/bash

(cd cadical-ple; make clean)
(cd extractor; make clean)
(cd tools/cadical; make clean)
(cd tools/encoders/knf2cnf; make clean)

(cd scripts; rm -r bins)