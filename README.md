# RTL Infrastructures for Hasunosora IC Design Club

## Introduction
This repository provides many RTL design infrastructures (modules, packages, definitions) to accelerate and simplify the design flow.
It is developed and maintained by the Hasunosora IC Design Club.

## License
This repository is licensed under the MIT License. 
You can freely use, modify, and distribute the code for both personal and commercial purposes,
as long as you include the original copyright and license notice in any copies or substantial portions of the
code.

See the [LICENSE](LICENSE) file for details.

## Dependency Management
This repository uses [FuseSoC](https://github.com/olofk/fusesoc) for dependency management.
You can use FuseSoC to easily integrate this repository into your own projects.

We provide a FuseSoC core descriptor file for each component in this repository.
You can add ANY components you want to your FuseSoC dependency list and use them in your designs.

Please refer to the FuseSoC documentation for more information on how to use it.

## Naming
All components in this repository follow the naming convention below:

```
hasunosora::<category>::<component_name>
```

### Category
Components in this repository are organized into the following categories:

| Category     | FuseSoC name | Description                                      |
|--------------|--------------|--------------------------------------------------|
| Arithmetic   | arith        | RTL modules for arithmetic, such as encoders, adder trees, comparators, etc.            |
| CDC          | cdc          | Clock Domain Crossing (CDC) modules.             |
| Datapath     | dpath        | General-purpose datapath modules, such as shift registers, etc.            |
| FIFO         | fifo         | Various FIFO modules.                            |
| Interface    | interface    | Modules for converting SystemVerilog interfaces to plain signals, and vice versa.  |
| Math         | math         | Modules and packages for mathematical operations |
| Memory       | memory       | Memory modules, such single/dual-port RAM, etc.  |
| Unit         | unit         | Basic building blocks, such as flip-flops, latches, etc.            |
| Infrastructure | ifr        | Basic infrastructure includes packages and type definitions.  |
| Verification  | verify      | Verification components (un-synthesizable) for verification. |

### Components
To get the full list of components available in this repository, please run the following command in the root of the repository with FuseSoC environment set up:

```bash
fusesoc --cores-root=proj core list
```

## Macros
### `DEFAULT_NETTYPE`
All RTL designs in this repository using following declaration at the beginning of each file:

```systemverilog
`default_nettype `DEFAULT_NETTYPE
```

This will set the default net type to `none` to avoid unintended implicit net declarations, which can lead to hard-to-debug issues. If your compiler or synthesis tool does not support this declaration, you can define the macro `USE_DEFAULT_NETTYPE_WIRE` to use the default net type as `wire`.

### `GENERATE_START` and `GENERATE_END`
In mordern SystemVerilog, the `generate` and `endgenerate` keywords are optional and can be omitted.
However, some older synthesis tools and simulators may not support this feature. To ensure compatibility with such tools, this repository uses the `GENERATE_START` and `GENERATE_END` macros to explicitly mark the beginning and end of generate blocks.
These macros can expand to `generate` and `endgenerate` if you define the `USE_EXPLICIT_GENERATE` macro while compiling your design.

### `LP_MODULE`
Mordern SystemVerilog supports the `localparam` keyword to define parameters that cannot be overridden on module parameter declaration area. We use this feature for some calculated values from parameters and this values need to be used on port. However, some older synthesis tools and simulators may not support this feature. To ensure compatibility with such tools, this repository uses the `LP_MODULE` macro to define such parameters. Defaultally, this macro expands to `localparam`, but if you define the `DONT_USE_LOCALPARAM_ON_MODULE` macro while compiling your design, it expands to `parameter` instead. (Note in this case, user may override such parameters on module parameter declaration area, may lead to unexpected behavior.)

### `ASYNC_REG_HINT`
For CDC (Clock Domain Crossing) modules, we use the `ASYNC_REG_HINT` macro (default expand to `(* ASYNC_REG = "TRUE" *)`) to provide synthesis tools with hints for implementing asynchronous registers. Some synthesis tools use other syntax for this purpose. You can redefine this macro to match the syntax required by your synthesis tool by defining the `ASYNC_REG_HINT` macro while compiling your design.

## Contribution
We welcome contributions from the community! If you find a bug or have a feature request, please open an issue on GitHub.
If you would like to contribute code, please fork the repository and submit a pull request.
