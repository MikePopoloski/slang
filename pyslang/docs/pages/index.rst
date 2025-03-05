Pyslang
===============

The Slang project contains Python bindings, packaged as a library called ``pyslang``.

This library provides a Pythonic interface to the Slang parser and evaluator, allowing you to load SystemVerilog source files, inspect the syntax tree, and evaluate expressions.

.. code-block:: bash

    pip install pyslang

or, to update your installed version to the latest release:

.. code-block:: bash

    pip install -U pyslang

or, to checkout and install a local build:

.. code-block:: bash

    git clone https://github.com/MikePopoloski/slang.git
    cd slang
    pip install .

Example Python Usage
====================

Given a ``test.sv`` source file:

.. code-block:: systemverilog

    module memory(
        address,
        data_in,
        data_out,
        read_write,
        chip_en
      );

      input wire [7:0] address, data_in;
      output reg [7:0] data_out;
      input wire read_write, chip_en;

      reg [7:0] mem [0:255];

      always @ (address or data_in or read_write or chip_en)
        if (read_write == 1 && chip_en == 1) begin
          mem[address] = data_in;
      end

      always @ (read_write or chip_en or address)
        if (read_write == 0 && chip_en)
          data_out = mem[address];
        else
          data_out = 0;

    endmodule

We can use slang to load the syntax tree and inspect it:

.. code-block:: python

    import pyslang

    tree = pyslang.SyntaxTree.fromFile('test.sv')
    mod = tree.root.members[0]
    print(mod.header.name.value)
    print(mod.members[0].kind)
    print(mod.members[1].header.dataType)

Expected output:

.. code-block:: text

    memory
    SyntaxKind.PortDeclaration
    reg [7:0]

We can also evaluate arbitrary SystemVerilog expressions:

.. code-block:: python

    session = pyslang.ScriptSession()
    session.eval("logic bit_arr [16] = '{0:1, 1:1, 2:1, default:0};")
    result = session.eval("bit_arr.sum with ( int'(item) );")
    print(result)

Expected output:

.. code-block:: text

    3
