#!/bin/bash
sed -e '/signal(SIGERR/s/^/\/\//' -i GKlib/error.c
