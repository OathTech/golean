package main

// Excluded by the leading underscore; if it were part of the package it
// would import os and run this init.
import "os"

func init() { fromImport = 100 + len(os.Args) }
