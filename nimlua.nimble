# Package

version       = "0.1.0"
author        = "hlaaftana"
description   = "lua backend for nim"
license       = "MIT"
srcDir        = "src"
installExt    = @["nim"]
bin           = @["nimlua"]

# Dependencies

requires "nim >= 1.0.6, compiler >= 1.0.6"
