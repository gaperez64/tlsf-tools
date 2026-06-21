# Third-party notices

## OxiDD

Repository: https://github.com/OxiDD/oxidd

Used through the `external/oxidd` submodule as the BDD backend for `tlsfcompose`
and `tlsfsolve`.

The OxiDD workspace declares:

```text
license = "MIT OR Apache-2.0"
```

The corresponding license files are `external/oxidd/LICENSE-MIT` and
`external/oxidd/LICENSE-APACHE` in the source tree.

MIT license notice:

```text
Copyright (c) 2022-2024 OxiDD Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

Apache-2.0 license terms are available at
https://www.apache.org/licenses/LICENSE-2.0 and in
`external/oxidd/LICENSE-APACHE`.

## Rust toolchain/cbindgen

Used at build time to produce the OxiDD C FFI header and static library.
