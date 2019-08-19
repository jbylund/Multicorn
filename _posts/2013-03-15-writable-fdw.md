---
layout: page
title: Writable FDW
---

A few days ago, an API for writable FDW has been committed to the postgresql
repository.

Multicorn is trying to implement this API, to make it easy for Python
developers to write FDW.

You can see the WIP on the `writable_fdw` branch on github:
https://github.com/Kozea/Multicorn/tree/writable_fdw

Documentation is lacking for now, and existing FDWs should be worked on to
implement the API.

You'll need the current dev version of postgresql to test it.

Any feedback is welcome!