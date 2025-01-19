slang-reflect
==================

slang-reflect is a tool that aims to help developers to remove the burden of creating `C/C++` representations of
SystemVerilog structs, enums and parameters. Its behavior is inspired from
the [verilator public](https://verilator.org/guide/latest/extensions.html#cmdoption-2) option provided by `verilator`,
and it is of a great use when building testbenches using `C++/SystemC`.

To indicate which SystemVerilog types we want to make public we need to annotate its declaration with `// public`
or `// verilator public`. For example:

```sv
typedef struct {
    logic k;
} pkg_struct_comment /* public */;

typedef enum {ONE = 2, TWO, THREE} my_enum /* public */;

localparam my_local /* public */ = 8'h42;
```

For all types that have been declared `public` inside the same `package` or `module`, the tool will create a header file
with a namespace inside it, both of them with the name of the SystemVerilog container. Inside the namespace, there will
be the declaration of the `public` types. For example, a SystemVerilog file that looks like this:

```sv
package foo;
    localparam foo_local /* public */ = 12;
endpackage

package bar;
    localparam bar_local /* public */ = 12;
endpackage

module top;
    localparam top_local /* verilator public */ = 12;
endmodule
```

The auto-generated files and code will look like this:

```cpp
// bar.h
#pragma once
#include ...

namespace bar {
    static constexpr uint32_t bar_local = 12;
}

// foo.h
#pragma once
#include ...

namespace foo {
    static constexpr uint32_t foo_local = 12;
}

// top.h
#pragma once
#include ...

namespace top {
    static constexpr uint32_t top_local = 12;
}
```

## CPP Reserved Keywords

Since not all CPP kewords are SystemVerilog keywords, if any name of a member, enum, struct or parameter collides with a
reserved C++ keyword, it will be renamed with a `_` in front. For example if a member of a struct is named <tt>operator</tt> it
will be emitted as `_operator`.

## SystemVerilog Namspace References

In order to handle references from other packages that are done using the `import foo::*` or `foo::my_local`, the foo
header will be included into the headers where their types or parameters are being used.

```sv
package bar;
    typedef struct packed {
        logic k;
    } bar_struct /* public */;
endpackage

package foo;
    typedef struct {
        bar::bar_struct foo_struct;
    } foo_struct /* public */;
endpackage
```

will transpile into

```cpp
// bar.h
#pragma once
#include ...

namespace bar {
    struct bar_struct {
        bool k;

        ...
    };
}

// foo.h
#pragma once
#include ...

#include "bar.h"

namespace foo {
    struct foo_struct {
        bar::bar_struct foo_struct;

        ...
    };
}
```

## SystemVerilog Typedefs

When the type of a member of a struct comes from a typedef, the tool will resolve the typedef and emit the base type.
For example:

```sv
package bar;
    typedef enum {ONE = 5, TWO, THREE} my_enum /* public */;
    typedef my_enum t_enum;
    typedef struct packed {
        t_enum e;
    } bar_struct /* public */;
endpackage
```

```cpp
// bar.h
#pragma once
#include ...

namespace bar {
    struct my_enum {
        enum Type : uint32_t {
            ONE = 5,
            TWO = 6,
            THREE = 7
        };
        ...
    };

    struct bar_struct {
        my_enum e;

        ...
    };
}
```

## Emitted Headers

The includes that are emitted along with each file are:

```cpp
#include <ostream>
#include <cstddef>
#include <cstdint>
#include <string>
#include <sstream>
#include <systemc.h>
```

The `#include <systemc.h>` can be removed if the `--no-sc` argument is provided to the tool.

## SystemVerilog Parameters

SystemVerilog parameters are transpiled as a `static constexpr` with the type being `uint32_t` or `uint64_t`. For
example

```sv
package foo;
    localparam bar /* public */ = 42;
endpackage
```

```cpp
namespace foo {
    static constexpr uint32_t bar = 42;
}
```

## SystemVerilog Enums

SystemVerilog enums are transpiled as a `struct` in order to provide convenient methods to serialize and deserialize the
enum into the underlying type. For example:

```sv
package bar;
    typedef enum {ONE = 5, TWO, THREE} my_enum /* public */;
endpackage
```

```cpp
// bar.h
#pragma once
#include ...

namespace bar {
    struct my_enum {
        enum Type : uint32_t {
            ONE = 5,
            TWO = 6,
            THREE = 7
        };

        static constexpr size_t _size = 32;

        Type type;
        my_enum() = default;
        my_enum (uint32_t data) {
            switch (data) {
                case 5: type = Type::ONE; break;
                case 6: type = Type::TWO; break;
                case 7: type = Type::THREE; break;
                default: throw std::runtime_error("Can not create my_enum from provided value");
            }
        }

        my_enum (Type& type) { this->type = type; }
        friend std::ostream& operator<<(std::ostream& os, const my_enum& data) {
            switch (data.type) {
                case Type::ONE: os << "ONE"; break;
                case Type::TWO: os << "TWO"; break;
                case Type::THREE: os << "THREE"; break;
            }
            return os;
        }

        my_enum& operator=(const Type t) {
            this->type = t;
            return *this;
        }

        operator uint64_t() const {
            return static_cast<uint64_t>(type);
        }

        Type operator() () const {
            return type;
        }

    };
}
```

## SystemVerilog Structs

SystemVerilog structs are transpiled as a `struct` that provide convenient methods to serialize, deserialize and print
the struct.

Members of the struct that are not another struct or enum, will be transpiled as `uint32_t`, `uint64_t` or `sc_bv<N>`.
In the case the option `--no-sc` has been provided to the tool and there is a member bigger than 64 bits, or the struct
itself has a size bigger than 64 bits, the tool will report an error asking for enabling the SystemC support.

For example:

```sv
package bar;
    typedef struct packed {
        logic [7:0]   b;
        logic [15:0]  h;
        logic [31:0]  w;
    } bar_struct /* public */;
endpackage
```

```cpp
// bar.h
#pragma once
#include ...

namespace bar {
    struct bar_struct {
        uint32_t w;
        uint32_t h;
        uint32_t b;

        static constexpr size_t w_s = 0;
        static constexpr size_t w_w = 32;
        static constexpr size_t h_s = 32;
        static constexpr size_t h_w = 16;
        static constexpr size_t b_s = 48;
        static constexpr size_t b_w = 8;
        static constexpr size_t _size = 56;

        bar_struct() = default;

        bar_struct(const uint64_t& data) {
            w = (data >> w_s) & (~0ULL >> (64 - 32));
            h = (data >> h_s) & (~0ULL >> (64 - 16));
            b = (data >> b_s) & (~0ULL >> (64 - 8));
        }

        bar_struct(const sc_bv<56>& data) {
            w = data.range(w_s + w_w - 1, w_s).to_uint64();
            h = data.range(h_s + h_w - 1, h_s).to_uint64();
            b = data.range(b_s + b_w - 1, b_s).to_uint64();
        }

        operator uint64_t() const {
            uint64_t ret = 0;
            ret |= static_cast<uint64_t>(w) << w_s;
            ret |= static_cast<uint64_t>(h) << h_s;
            ret |= static_cast<uint64_t>(b) << b_s;
            return ret;
        }

        operator sc_bv<56>() const {
            auto ret = sc_bv<56>();
            ret.range(w_s + w_w - 1, w_s) = w;
            ret.range(h_s + h_w - 1, h_s) = h;
            ret.range(b_s + b_w - 1, b_s) = b;
            return ret;
        }

        std::string to_string() const {
            std::stringstream ss;
            ss << "w" << " = " << w;
            ss << " h" << " = " << h;
            ss << " b" << " = " << b;
            return ss.str();
        }

        friend std::ostream& operator<<(std::ostream& os, const bar_struct& data) {
            os << data.to_string();
            return os;
        }
        static uint32_t get_w (const uint64_t& data) {
            return (data >> w_s) & (~0ULL >> (64 - 32));
        }
        static uint32_t get_h (const uint64_t& data) {
            return (data >> h_s) & (~0ULL >> (64 - 16));
        }
        static uint32_t get_b (const uint64_t& data) {
            return (data >> b_s) & (~0ULL >> (64 - 8));
        }
    };
}
```
