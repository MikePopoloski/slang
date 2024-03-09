# SystemVerilog
## A.1 Source text
### A.1.1 Library source text
<a name="library_text"></a>library\_text ::= \{ [library_description](#library_description) }  
<a name="library_description"></a>library\_description ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[library_declaration](#library_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [include_statement](#include_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [config_declaration](#config_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="library_declaration"></a>library\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[library](#library) [library_identifier](#library_identifier) [file_path_spec](#file_path_spec) \{ `,` [file_path_spec](#file_path_spec) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `-`[incdir](#incdir) [file_path_spec](#file_path_spec) \{ `,` [file_path_spec](#file_path_spec) } ] `;`  
<a name="include_statement"></a>include\_statement ::= [include](#include) [file_path_spec](#file_path_spec) `;`  
### A.1.2 SystemVerilog source text
<a name="source_text"></a>source\_text ::= \[ [timeunits_declaration](#timeunits_declaration) ] \{ [description](#description) }  
<a name="description"></a>description ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_declaration](#module_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [udp_declaration](#udp_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_declaration](#interface_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_declaration](#program_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [package_declaration](#package_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [package_item](#package_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [bind_directive](#bind_directive)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [config_declaration](#config_declaration)  
<a name="module_nonansi_header"></a>module\_nonansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [module_keyword](#module_keyword) \[ [lifetime](#lifetime) ] [module_identifier](#module_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) } \[ [parameter_port_list](#parameter_port_list) ] [list_of_ports](#list_of_ports) `;`  
<a name="module_ansi_header"></a>module\_ansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [module_keyword](#module_keyword) \[ [lifetime](#lifetime) ] [module_identifier](#module_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) }[1](#1) \[ [parameter_port_list](#parameter_port_list) ] \[ [list_of_port_declarations](#list_of_port_declarations) ] `;`  
<a name="module_declaration"></a>module\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_nonansi_header](#module_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [module_item](#module_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endmodule](#endmodule) \[ `:` [module_identifier](#module_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_ansi_header](#module_ansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [non_port_module_item](#non_port_module_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endmodule](#endmodule) \[ `:` [module_identifier](#module_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [module_keyword](#module_keyword) \[ [lifetime](#lifetime) ] [module_identifier](#module_identifier) `(` `.` `*` `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [module_item](#module_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endmodule](#endmodule) \[ `:` [module_identifier](#module_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [module_nonansi_header](#module_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [module_ansi_header](#module_ansi_header)  
<a name="module_keyword"></a>module\_keyword ::= [module](#module) \| [macromodule](#macromodule)  
<a name="interface_declaration"></a>interface\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface_nonansi_header](#interface_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [interface_item](#interface_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endinterface](#endinterface) \[ `:` [interface_identifier](#interface_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_ansi_header](#interface_ansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [non_port_interface_item](#non_port_interface_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endinterface](#endinterface) \[ `:` [interface_identifier](#interface_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [interface](#interface) [interface_identifier](#interface_identifier) `(` `.` `*` `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [interface_item](#interface_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endinterface](#endinterface) \[ `:` [interface_identifier](#interface_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [interface_nonansi_header](#interface_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [interface_ansi_header](#interface_ansi_header)  
<a name="interface_nonansi_header"></a>interface\_nonansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [interface](#interface) \[ [lifetime](#lifetime) ] [interface_identifier](#interface_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) } \[ [parameter_port_list](#parameter_port_list) ] [list_of_ports](#list_of_ports) `;`  
<a name="interface_ansi_header"></a>interface\_ansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [interface](#interface) \[ [lifetime](#lifetime) ] [interface_identifier](#interface_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) }[1](#1) \[ [parameter_port_list](#parameter_port_list) ] \[ [list_of_port_declarations](#list_of_port_declarations) ] `;`  
<a name="program_declaration"></a>program\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[program_nonansi_header](#program_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [program_item](#program_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endprogram](#endprogram) \[ `:` [program_identifier](#program_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_ansi_header](#program_ansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [non_port_program_item](#non_port_program_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endprogram](#endprogram) \[ `:` [program_identifier](#program_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [program](#program) [program_identifier](#program_identifier) `(` `.` `*` `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ [program_item](#program_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endprogram](#endprogram) \[ `:` [program_identifier](#program_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [program_nonansi_header](#program_nonansi_header)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [program_ansi_header](#program_ansi_header)  
<a name="program_nonansi_header"></a>program\_nonansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [program](#program) \[ [lifetime](#lifetime) ] [program_identifier](#program_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) } \[ [parameter_port_list](#parameter_port_list) ] [list_of_ports](#list_of_ports) `;`  
<a name="program_ansi_header"></a>program\_ansi\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [program](#program) \[ [lifetime](#lifetime) ] [program_identifier](#program_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [package_import_declaration](#package_import_declaration) }[1](#1) \[ [parameter_port_list](#parameter_port_list) ] \[ [list_of_port_declarations](#list_of_port_declarations) ] `;`  
<a name="checker_declaration"></a>checker\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[checker](#checker) [checker_identifier](#checker_identifier) \[ `(` \[ [checker_port_list](#checker_port_list) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ \{ [attribute_instance](#attribute_instance) } [checker_or_generate_item](#checker_or_generate_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endchecker](#endchecker) \[ `:` [checker_identifier](#checker_identifier) ]  
<a name="class_declaration"></a>class\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [virtual](#virtual) ] [class](#class) \[ [final_specifier](#final_specifier) ] [class_identifier](#class_identifier) \[ [parameter_port_list](#parameter_port_list) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [extends](#extends) [class_type](#class_type) \[ `(` \[ [list_of_arguments](#list_of_arguments) \| [default](#default) ] `)` ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [implements](#implements) [interface_class_type](#interface_class_type) \{ `,` [interface_class_type](#interface_class_type) } ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [class_item](#class_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endclass](#endclass) \[ `:` [class_identifier](#class_identifier) ]  
<a name="interface_class_declaration"></a>interface\_class\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface](#interface) [class](#class) [class_identifier](#class_identifier) \[ [parameter_port_list](#parameter_port_list) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [extends](#extends) [interface_class_type](#interface_class_type) \{ `,` [interface_class_type](#interface_class_type) } ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [interface_class_item](#interface_class_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endclass](#endclass) \[ `:` [class_identifier](#class_identifier) ]  
<a name="package_declaration"></a>package\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [package](#package) \[ [lifetime](#lifetime) ] [package_identifier](#package_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timeunits_declaration](#timeunits_declaration) ] \{ \{ [attribute_instance](#attribute_instance) } [package_item](#package_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endpackage](#endpackage) \[ `:` [package_identifier](#package_identifier) ]  
<a name="timeunits_declaration"></a>timeunits\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[timeunit](#timeunit) [time_literal](#time_literal) \[ `/` [time_literal](#time_literal) ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeprecision](#timeprecision) [time_literal](#time_literal) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeunit](#timeunit) [time_literal](#time_literal) `;` [timeprecision](#timeprecision) [time_literal](#time_literal) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeprecision](#timeprecision) [time_literal](#time_literal) `;` [timeunit](#timeunit) [time_literal](#time_literal) `;`  
### A.1.3 Module parameters and ports
<a name="parameter_port_list"></a>parameter\_port\_list ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`#` `(` [list_of_param_assignments](#list_of_param_assignments) \{ `,` [parameter_port_declaration](#parameter_port_declaration) } `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `#` `(` [parameter_port_declaration](#parameter_port_declaration) \{ `,` [parameter_port_declaration](#parameter_port_declaration) } `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `#(` `)`  
<a name="parameter_port_declaration"></a>parameter\_port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[parameter_declaration](#parameter_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [local_parameter_declaration](#local_parameter_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [data_type](#data_type) [list_of_param_assignments](#list_of_param_assignments)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_parameter_declaration](#type_parameter_declaration)  
<a name="list_of_ports"></a>list\_of\_ports ::= `(` [port](#port) \{ `,` [port](#port) } `)`  
<a name="list_of_port_declarations2"></a>list\_of\_port\_declarations2 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` \[ \{ [attribute_instance](#attribute_instance) } [ansi_port_declaration](#ansi_port_declaration) \{ `,` \{ [attribute_instance](#attribute_instance) } [ansi_port_declaration](#ansi_port_declaration) } ] `)`  
<a name="port_declaration"></a>port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [inout_declaration](#inout_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [input_declaration](#input_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [output_declaration](#output_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [ref_declaration](#ref_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [interface_port_declaration](#interface_port_declaration)  
<a name="port"></a>port ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [port_expression](#port_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [port_identifier](#port_identifier) `(` \[ [port_expression](#port_expression) ] `)`  
<a name="port_expression"></a>port\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_reference](#port_reference)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [port_reference](#port_reference) \{ `,` [port_reference](#port_reference) } }  
<a name="port_reference"></a>port\_reference ::= [port_identifier](#port_identifier) [constant_select](#constant_select)  
<a name="port_direction"></a>port\_direction ::= [input](#input) \| [output](#output) \| [inout](#inout) \| [ref](#ref)  
<a name="net_port_header"></a>net\_port\_header ::= \[ [port_direction](#port_direction) ] [net_port_type](#net_port_type)  
<a name="variable_port_header"></a>variable\_port\_header ::= \[ [port_direction](#port_direction) ] [variable_port_type](#variable_port_type)  
<a name="interface_port_header"></a>interface\_port\_header ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface_identifier](#interface_identifier) \[ `.` [modport_identifier](#modport_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface](#interface) \[ `.` [modport_identifier](#modport_identifier) ]  
<a name="ansi_port_declaration"></a>ansi\_port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [net_port_header](#net_port_header) \| [interface_port_header](#interface_port_header) ] [port_identifier](#port_identifier) \{ [unpacked_dimension](#unpacked_dimension) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `=` [constant_expression](#constant_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [variable_port_header](#variable_port_header) ] [port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [constant_expression](#constant_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [port_direction](#port_direction) ] `.` [port_identifier](#port_identifier) `(` \[ [expression](#expression) ] `)`  
### A.1.4 Module items
<a name="severity_system_task"></a>severity\_system\_task ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[fatal](#fatal)   \[ `(` [finish_number](#finish_number) `[,` [list_of_arguments](#list_of_arguments) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[error](#error)   \[ `(` \[ [list_of_arguments](#list_of_arguments) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[warning](#warning) \[ `(` \[ [list_of_arguments](#list_of_arguments) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[info](#info)    \[ `(` \[ [list_of_arguments](#list_of_arguments) ] `)` ] `;`  
<a name="finish_number"></a>finish\_number ::= [0](#0) \| [1](#1) \| [2](#2)  
<a name="elaboration_severity_system_task"></a>elaboration\_severity\_system\_task ::= [severity_system_task](#severity_system_task)  
<a name="module_common_item"></a>module\_common\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_or_generate_item_declaration](#module_or_generate_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_instantiation](#interface_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_instantiation](#program_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assertion_item](#assertion_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [bind_directive](#bind_directive)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [continuous_assign](#continuous_assign)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [net_alias](#net_alias)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [initial_construct](#initial_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [final_construct](#final_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [always_construct](#always_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [loop_generate_construct](#loop_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [conditional_generate_construct](#conditional_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [elaboration_severity_system_task](#elaboration_severity_system_task)  
<a name="module_item"></a>module\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_declaration](#port_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [non_port_module_item](#non_port_module_item)  
<a name="module_or_generate_item"></a>module\_or\_generate\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [parameter_override](#parameter_override)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [gate_instantiation](#gate_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [udp_instantiation](#udp_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [module_instantiation](#module_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [module_common_item](#module_common_item)  
<a name="module_or_generate_item_declaration"></a>module\_or\_generate\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[package_or_generate_item_declaration](#package_or_generate_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [genvar_declaration](#genvar_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_declaration](#clocking_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) [clocking](#clocking) [clocking_identifier](#clocking_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) [disable](#disable) [iff](#iff) [expression_or_dist](#expression_or_dist) `;`  
<a name="non_port_module_item"></a>non\_port\_module\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[generate_region](#generate_region)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_or_generate_item](#module_or_generate_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [specify_block](#specify_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [specparam_declaration](#specparam_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_declaration](#program_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_declaration](#module_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_declaration](#interface_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeunits_declaration3](#timeunits_declaration3)  
<a name="parameter_override"></a>parameter\_override ::= [defparam](#defparam) [list_of_defparam_assignments](#list_of_defparam_assignments) `;`  
<a name="bind_directive4"></a>bind\_directive4 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[bind](#bind) [bind_target_scope](#bind_target_scope) \[ `:` [bind_target_instance_list](#bind_target_instance_list) ] [bind_instantiation](#bind_instantiation) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [bind](#bind) [bind_target_instance](#bind_target_instance) [bind_instantiation](#bind_instantiation) `;`  
<a name="bind_target_scope"></a>bind\_target\_scope ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_identifier](#module_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_identifier](#interface_identifier)  
<a name="bind_target_instance"></a>bind\_target\_instance ::= [hierarchical_identifier](#hierarchical_identifier) [constant_bit_select](#constant_bit_select)  
<a name="bind_target_instance_list"></a>bind\_target\_instance\_list ::= [bind_target_instance](#bind_target_instance) \{ `,` [bind_target_instance](#bind_target_instance) }  
<a name="bind_instantiation"></a>bind\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[program_instantiation](#program_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_instantiation](#module_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_instantiation](#interface_instantiation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_instantiation](#checker_instantiation)  
### A.1.5 Configuration source text
<a name="config_declaration"></a>config\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[config](#config) [config_identifier](#config_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [local_parameter_declaration](#local_parameter_declaration) `;` }  
&nbsp;&nbsp;&nbsp;&nbsp;[design_statement](#design_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [config_rule_statement](#config_rule_statement) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endconfig](#endconfig) \[ `:` [config_identifier](#config_identifier) ]  
<a name="design_statement"></a>design\_statement ::= [design](#design) \{ \[ [library_identifier](#library_identifier) `.` ] [cell_identifier](#cell_identifier) } `;`  
<a name="config_rule_statement"></a>config\_rule\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[default_clause](#default_clause) [liblist_clause](#liblist_clause) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inst_clause](#inst_clause) [liblist_clause](#liblist_clause) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inst_clause](#inst_clause) [use_clause](#use_clause) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cell_clause](#cell_clause) [liblist_clause](#liblist_clause) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cell_clause](#cell_clause) [use_clause](#use_clause) `;`  
<a name="default_clause"></a>default\_clause ::= [default](#default)  
<a name="inst_clause"></a>inst\_clause ::= [instance](#instance) [inst_name](#inst_name)  
<a name="inst_name"></a>inst\_name ::= [topmodule_identifier](#topmodule_identifier) \{ `.` [instance_identifier](#instance_identifier) }  
<a name="cell_clause"></a>cell\_clause ::= [cell](#cell) \[ [library_identifier](#library_identifier) `.` ] [cell_identifier](#cell_identifier)  
<a name="liblist_clause"></a>liblist\_clause ::= [liblist](#liblist) \{ [library_identifier](#library_identifier) }  
<a name="use_clause"></a>use\_clause ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[use](#use) \[ [library_identifier](#library_identifier) `.` ] [cell_identifier](#cell_identifier) \[ `:` [config](#config) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [use](#use) [named_parameter_assignment](#named_parameter_assignment) \{ `,` [named_parameter_assignment](#named_parameter_assignment) } \[ `:` [config](#config) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [use](#use) \[ [library_identifier](#library_identifier) `.` ] [cell_identifier](#cell_identifier) [named_parameter_assignment](#named_parameter_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ `,` [named_parameter_assignment](#named_parameter_assignment) } \[ `:` [config](#config) ]  
### A.1.6 Interface items
<a name="interface_or_generate_item"></a>interface\_or\_generate\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [module_common_item](#module_common_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [extern_tf_declaration](#extern_tf_declaration)  
<a name="extern_tf_declaration"></a>extern\_tf\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[extern](#extern) [method_prototype](#method_prototype) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [forkjoin](#forkjoin) [task_prototype](#task_prototype) `;`  
<a name="interface_item"></a>interface\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_declaration](#port_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [non_port_interface_item](#non_port_interface_item)  
<a name="non_port_interface_item"></a>non\_port\_interface\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[generate_region](#generate_region)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_or_generate_item](#interface_or_generate_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_declaration](#program_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [modport_declaration](#modport_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_declaration](#interface_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeunits_declaration3](#timeunits_declaration3)  
### A.1.7 Program items
<a name="program_item"></a>program\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_declaration](#port_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [non_port_program_item](#non_port_program_item)  
<a name="non_port_program_item"></a>non\_port\_program\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [continuous_assign](#continuous_assign)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [module_or_generate_item_declaration](#module_or_generate_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [initial_construct](#initial_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [final_construct](#final_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [concurrent_assertion_item](#concurrent_assertion_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeunits_declaration3](#timeunits_declaration3)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [program_generate_item](#program_generate_item)  
<a name="program_generate_item5"></a>program\_generate\_item5 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[loop_generate_construct](#loop_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [conditional_generate_construct](#conditional_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [generate_region](#generate_region)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [elaboration_severity_system_task](#elaboration_severity_system_task)  
### A.1.8 Checker items
<a name="checker_port_list"></a>checker\_port\_list ::= [checker_port_item](#checker_port_item) \{ `,` [checker_port_item](#checker_port_item) }  
<a name="checker_port_item"></a>checker\_port\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } \[ [checker_port_direction](#checker_port_direction) ] [property_formal_type](#property_formal_type) [formal_port_identifier](#formal_port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [variable_dimension](#variable_dimension) } \[ `=` [property_actual_arg](#property_actual_arg) ]  
<a name="checker_port_direction"></a>checker\_port\_direction ::= [input](#input) \| [output](#output)  
<a name="checker_or_generate_item"></a>checker\_or\_generate\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[checker_or_generate_item_declaration](#checker_or_generate_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [initial_construct](#initial_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [always_construct](#always_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [final_construct](#final_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assertion_item](#assertion_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [continuous_assign](#continuous_assign)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_generate_item](#checker_generate_item)  
<a name="checker_or_generate_item_declaration"></a>checker\_or\_generate\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [rand](#rand) ] [data_declaration](#data_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_declaration](#function_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_declaration](#checker_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assertion_item_declaration](#assertion_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [covergroup_declaration](#covergroup_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [genvar_declaration](#genvar_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_declaration](#clocking_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) [clocking](#clocking) [clocking_identifier](#clocking_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) [disable](#disable) [iff](#iff) [expression_or_dist](#expression_or_dist) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="checker_generate_item6"></a>checker\_generate\_item6 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[loop_generate_construct](#loop_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [conditional_generate_construct](#conditional_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [generate_region](#generate_region)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [elaboration_severity_system_task](#elaboration_severity_system_task)  
### A.1.9 Class items
<a name="class_item"></a>class\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [class_property](#class_property)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [class_method](#class_method)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [class_constraint](#class_constraint)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [class_declaration](#class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [interface_class_declaration](#interface_class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [covergroup_declaration](#covergroup_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [local_parameter_declaration](#local_parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [parameter_declaration7](#parameter_declaration7) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="class_property"></a>class\_property ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [property_qualifier](#property_qualifier) } [data_declaration](#data_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [const](#const) \{ [class_item_qualifier](#class_item_qualifier) } [data_type](#data_type) [const_identifier](#const_identifier) \[ `=` [constant_expression](#constant_expression) ] `;`  
<a name="class_method"></a>class\_method ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [method_qualifier](#method_qualifier) } [task_declaration](#task_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [method_qualifier](#method_qualifier) } [function_declaration](#function_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pure](#pure) [virtual](#virtual) \{ [class_item_qualifier](#class_item_qualifier) } [method_prototype8](#method_prototype8) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) \{ [method_qualifier](#method_qualifier) } [method_prototype](#method_prototype) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [method_qualifier](#method_qualifier) } [class_constructor_declaration](#class_constructor_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) \{ [method_qualifier](#method_qualifier) } [class_constructor_prototype](#class_constructor_prototype)  
<a name="class_constructor_declaration"></a>class\_constructor\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function](#function) \[ [class_scope](#class_scope) ] [new](#new) \[ `(` \[ [class_constructor_arg_list](#class_constructor_arg_list) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [block_item_declaration](#block_item_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [super](#super) `.` [new](#new) \[ `(` \[ [list_of_arguments](#list_of_arguments) \| [default](#default) ] `)` ] `;` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [function_statement_or_null](#function_statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endfunction](#endfunction) \[ `:` [new](#new) ]  
<a name="class_constructor_prototype"></a>class\_constructor\_prototype ::= [function](#function) [new](#new) \[ `(` \[ [class_constructor_arg_list](#class_constructor_arg_list) ] `)` ] `;`  
<a name="class_constructor_arg_list"></a>class\_constructor\_arg\_list ::= [class_constructor_arg](#class_constructor_arg) \{ `,` [class_constructor_arg](#class_constructor_arg) }[9](#9)  
<a name="class_constructor_arg"></a>class\_constructor\_arg ::= [tf_port_item](#tf_port_item) \| [default](#default)  
<a name="interface_class_item"></a>interface\_class\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[type_declaration](#type_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [interface_class_method](#interface_class_method)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [local_parameter_declaration](#local_parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [parameter_declaration7](#parameter_declaration7) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="interface_class_method"></a>interface\_class\_method ::= [pure](#pure) [virtual](#virtual) [method_prototype](#method_prototype) `;`  
<a name="class_constraint"></a>class\_constraint ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constraint_prototype](#constraint_prototype)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constraint_declaration](#constraint_declaration)  
<a name="class_item_qualifier10"></a>class\_item\_qualifier10 ::= [static](#static) \| [protected](#protected) \| [local](#local)  
<a name="property_qualifier10"></a>property\_qualifier10 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[random_qualifier](#random_qualifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_item_qualifier](#class_item_qualifier)  
<a name="random_qualifier10"></a>random\_qualifier10 ::= [rand](#rand) \| [randc](#randc)  
<a name="method_qualifier10"></a>method\_qualifier10 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [pure](#pure) ] [virtual](#virtual)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_item_qualifier](#class_item_qualifier)  
<a name="method_prototype"></a>method\_prototype ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[task_prototype](#task_prototype)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_prototype](#function_prototype)  
### A.1.10 Constraints
<a name="constraint_declaration"></a>constraint\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [static](#static) ] [constraint](#constraint) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][11](#11) [constraint_identifier](#constraint_identifier) [constraint_block](#constraint_block)  
<a name="constraint_block"></a>constraint\_block ::= \{ \{ [constraint_block_item](#constraint_block_item) } }  
<a name="constraint_block_item"></a>constraint\_block\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[solve](#solve) [solve_before_list](#solve_before_list) [before](#before) [solve_before_list](#solve_before_list) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constraint_expression](#constraint_expression)  
<a name="solve_before_list"></a>solve\_before\_list ::= [constraint_primary](#constraint_primary) \{ `,` [constraint_primary](#constraint_primary) }  
<a name="constraint_primary"></a>constraint\_primary ::= \[ [implicit_class_handle](#implicit_class_handle) `.` \| [class_scope](#class_scope) ] [hierarchical_identifier](#hierarchical_identifier) [select](#select) \[ `(` `)` ][12](#12)  
<a name="constraint_expression"></a>constraint\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [soft](#soft) ] [expression_or_dist](#expression_or_dist) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [uniqueness_constraint](#uniqueness_constraint) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) [â](#â)`€“>` [constraint_set](#constraint_set)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [if](#if) `(` [expression](#expression) `)` [constraint_set](#constraint_set) \[ [else](#else) [constraint_set](#constraint_set) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [foreach](#foreach) `(` [ps_or_hierarchical_array_identifier](#ps_or_hierarchical_array_identifier) \[ [loop_variables](#loop_variables) ] `)` [constraint_set](#constraint_set)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [disable](#disable) [soft](#soft) [constraint_primary](#constraint_primary) `;`  
<a name="uniqueness_constraint"></a>uniqueness\_constraint ::= [unique](#unique) \{ [range_list13](#range_list13) }  
<a name="constraint_set"></a>constraint\_set ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constraint_expression](#constraint_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ \{ [constraint_expression](#constraint_expression) } }  
<a name="expression_or_dist"></a>expression\_or\_dist ::= [expression](#expression) \[ [dist](#dist) \{ [dist_list](#dist_list) } ]  
<a name="dist_list"></a>dist\_list ::= [dist_item](#dist_item) \{ `,` [dist_item](#dist_item) }  
<a name="dist_item"></a>dist\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[value_range](#value_range) \[ [dist_weight](#dist_weight) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) `:/` [expression](#expression)  
<a name="dist_weight"></a>dist\_weight ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`:=` [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `:/` [expression](#expression)  
<a name="constraint_prototype"></a>constraint\_prototype ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [constraint_prototype_qualifier](#constraint_prototype_qualifier) ] \[ [static](#static) ] [constraint](#constraint) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][8](#8)`,`[11](#11)  
&nbsp;&nbsp;&nbsp;&nbsp;[constraint_identifier](#constraint_identifier) `;`  
<a name="constraint_prototype_qualifier"></a>constraint\_prototype\_qualifier ::= [extern](#extern) \| [pure](#pure)  
<a name="extern_constraint_declaration"></a>extern\_constraint\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [static](#static) ] [constraint](#constraint) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][11](#11) [class_scope](#class_scope) [constraint_identifier](#constraint_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;[constraint_block](#constraint_block)  
### A.1.11 Package items
<a name="package_item"></a>package\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[package_or_generate_item_declaration](#package_or_generate_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [anonymous_program](#anonymous_program)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [package_export_declaration](#package_export_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [timeunits_declaration3](#timeunits_declaration3)  
<a name="package_or_generate_item_declaration"></a>package\_or\_generate\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[net_declaration](#net_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [data_declaration](#data_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [task_declaration](#task_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_declaration](#function_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_declaration](#checker_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [dpi_import_export](#dpi_import_export)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern_constraint_declaration](#extern_constraint_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_declaration](#class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_class_declaration](#interface_class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_constructor_declaration](#class_constructor_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [local_parameter_declaration](#local_parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [parameter_declaration](#parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [covergroup_declaration](#covergroup_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assertion_item_declaration](#assertion_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="anonymous_program"></a>anonymous\_program ::= [program](#program) `;` \{ [anonymous_program_item](#anonymous_program_item) } [endprogram](#endprogram)  
<a name="anonymous_program_item"></a>anonymous\_program\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[task_declaration](#task_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_declaration](#function_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_declaration](#class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_class_declaration](#interface_class_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [covergroup_declaration](#covergroup_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_constructor_declaration](#class_constructor_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
## A.2 Declarations
### A.2.1 Declaration types
#### A.2.1.1 Module parameter declarations
<a name="local_parameter_declaration"></a>local\_parameter\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[localparam](#localparam) [data_type_or_implicit](#data_type_or_implicit) [list_of_param_assignments](#list_of_param_assignments)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [localparam](#localparam) [type_parameter_declaration](#type_parameter_declaration)  
<a name="parameter_declaration"></a>parameter\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[parameter](#parameter) [data_type_or_implicit](#data_type_or_implicit) [list_of_param_assignments](#list_of_param_assignments)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [parameter](#parameter) [type_parameter_declaration](#type_parameter_declaration)  
<a name="type_parameter_declaration"></a>type\_parameter\_declaration ::= [type](#type) \[ [forward_type](#forward_type) ] [list_of_type_assignments](#list_of_type_assignments)  
<a name="specparam_declaration"></a>specparam\_declaration ::= [specparam](#specparam) \[ [packed_dimension](#packed_dimension) ] [list_of_specparam_assignments](#list_of_specparam_assignments) `;`  
#### A.2.1.2 Port declarations
<a name="inout_declaration"></a>inout\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[inout](#inout) [net_port_type](#net_port_type) [list_of_port_identifiers](#list_of_port_identifiers)  
<a name="input_declaration"></a>input\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[input](#input) [net_port_type](#net_port_type) [list_of_port_identifiers](#list_of_port_identifiers)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [input](#input) [variable_port_type](#variable_port_type) [list_of_variable_identifiers](#list_of_variable_identifiers)  
<a name="output_declaration"></a>output\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[output](#output) [net_port_type](#net_port_type) [list_of_port_identifiers](#list_of_port_identifiers)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [output](#output) [variable_port_type](#variable_port_type) [list_of_variable_port_identifiers](#list_of_variable_port_identifiers)  
<a name="interface_port_declaration"></a>interface\_port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface_identifier](#interface_identifier) [list_of_interface_identifiers](#list_of_interface_identifiers)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_identifier](#interface_identifier) `.` [modport_identifier](#modport_identifier) [list_of_interface_identifiers](#list_of_interface_identifiers)  
<a name="ref_declaration"></a>ref\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ref](#ref) [variable_port_type](#variable_port_type)  [list_of_variable_identifiers](#list_of_variable_identifiers)  
#### A.2.1.3 Type declarations
<a name="data_declaration"></a>data\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [const](#const) ] \[ [var](#var) ] \[ [lifetime](#lifetime) ] [data_type_or_implicit](#data_type_or_implicit) [list_of_variable_decl_assignments](#list_of_variable_decl_assignments) `;`[14](#14)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_declaration](#type_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [package_import_declaration15](#package_import_declaration15)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nettype_declaration](#nettype_declaration)  
<a name="package_import_declaration"></a>package\_import\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[import](#import) [package_import_item](#package_import_item) \{ `,` [package_import_item](#package_import_item) } `;`  
<a name="package_export_declaration"></a>package\_export\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[export](#export) `*::*` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [export](#export) [package_import_item](#package_import_item) \{ `,` [package_import_item](#package_import_item) } `;`  
<a name="package_import_item"></a>package\_import\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[package_identifier](#package_identifier) `::` [identifier](#identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [package_identifier](#package_identifier) `::` `*`  
<a name="genvar_declaration"></a>genvar\_declaration ::= [genvar](#genvar) [list_of_genvar_identifiers](#list_of_genvar_identifiers) `;`  
<a name="net_declaration16"></a>net\_declaration16 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[net_type](#net_type) \[ [drive_strength](#drive_strength) \| [charge_strength](#charge_strength) ] \[ [vectored](#vectored) \| [scalared](#scalared) ]  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type_or_implicit](#data_type_or_implicit) \[ [delay3](#delay3) ] [list_of_net_decl_assignments](#list_of_net_decl_assignments) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nettype_identifier](#nettype_identifier) \[ [delay_control](#delay_control) ] [list_of_net_decl_assignments](#list_of_net_decl_assignments) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interconnect](#interconnect) [implicit_data_type](#implicit_data_type) \[ `#` [delay_value](#delay_value) ]  
&nbsp;&nbsp;&nbsp;&nbsp;[net_identifier](#net_identifier) \{ [unpacked_dimension](#unpacked_dimension) } \[ `,` [net_identifier](#net_identifier) \{ [unpacked_dimension](#unpacked_dimension) } ] `;`  
<a name="type_declaration"></a>type\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[typedef](#typedef) [data_type_or_incomplete_class_scoped_type](#data_type_or_incomplete_class_scoped_type) [type_identifier](#type_identifier) \{ [variable_dimension](#variable_dimension) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [typedef](#typedef) [interface_port_identifier](#interface_port_identifier) [constant_bit_select](#constant_bit_select) `.` [type_identifier](#type_identifier) [type_identifier](#type_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [typedef](#typedef) \[ [forward_type](#forward_type) ] [type_identifier](#type_identifier) `;`  
<a name="forward_type"></a>forward\_type ::= [enum](#enum) \| [struct](#struct) \| [union](#union) \| [class](#class) \| [interface](#interface) [class](#class)  
<a name="nettype_declaration"></a>nettype\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[nettype](#nettype) [data_type](#data_type) [nettype_identifier](#nettype_identifier) \[ [with](#with) \[ [package_scope](#package_scope) \| [class_scope](#class_scope) ] [tf_identifier](#tf_identifier) ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nettype](#nettype) \[ [package_scope](#package_scope) \| [class_scope](#class_scope) ] [nettype_identifier](#nettype_identifier) [nettype_identifier](#nettype_identifier) `;`  
<a name="lifetime"></a>lifetime ::= [static](#static) \| [automatic](#automatic)  
### A.2.2 Declaration data types
#### A.2.2.1 Net and variable types
<a name="casting_type"></a>casting\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[simple_type](#simple_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_primary](#constant_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [signing](#signing)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [string](#string)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [const](#const)  
<a name="data_type"></a>data\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integer_vector_type](#integer_vector_type) \[ [signing](#signing) ] \{ [packed_dimension](#packed_dimension) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [integer_atom_type](#integer_atom_type) \[ [signing](#signing) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [non_integer_type](#non_integer_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [struct_union](#struct_union) \[ [packed](#packed) \[ [signing](#signing) ] ] \{ [struct_union_member](#struct_union_member) \{ [struct_union_member](#struct_union_member) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [packed_dimension](#packed_dimension) }[17](#17)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [enum](#enum) \[ [enum_base_type](#enum_base_type) ] \{ [enum_name_declaration](#enum_name_declaration) \{ `,` [enum_name_declaration](#enum_name_declaration) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [packed_dimension](#packed_dimension) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [string](#string)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [chandle](#chandle)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [virtual](#virtual) \[ [interface](#interface) ] [interface_identifier](#interface_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ] \[ `.` [modport_identifier](#modport_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [class_scope](#class_scope) \| [package_scope](#package_scope) ] [type_identifier](#type_identifier) \{ [packed_dimension](#packed_dimension) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_type](#class_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event](#event)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_covergroup_identifier](#ps_covergroup_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_reference18](#type_reference18)  
<a name="data_type_or_implicit"></a>data\_type\_or\_implicit ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type](#data_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [implicit_data_type](#implicit_data_type)  
<a name="implicit_data_type"></a>implicit\_data\_type ::= \[ [signing](#signing) ] \{ [packed_dimension](#packed_dimension) }  
<a name="enum_base_type"></a>enum\_base\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integer_atom_type](#integer_atom_type) \[ [signing](#signing) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [integer_vector_type](#integer_vector_type) \[ [signing](#signing) ] \[ [packed_dimension](#packed_dimension) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_identifier](#type_identifier) \[ [packed_dimension](#packed_dimension) ][19](#19)  
<a name="enum_name_declaration"></a>enum\_name\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[enum_identifier](#enum_identifier) \[ \[ [integral_number](#integral_number) \[ `:` [integral_number](#integral_number) ] ] ] \[ `=` [constant_expression](#constant_expression) ]  
<a name="class_scope"></a>class\_scope ::= [class_type](#class_type) `::`  
<a name="class_type"></a>class\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ps_class_identifier](#ps_class_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\{ `::` [class_identifier](#class_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ] }  
<a name="interface_class_type"></a>interface\_class\_type ::= [ps_class_identifier](#ps_class_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ]  
<a name="integer_type"></a>integer\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integer_vector_type](#integer_vector_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [integer_atom_type](#integer_atom_type)  
<a name="integer_atom_type"></a>integer\_atom\_type ::= [byte](#byte) \| [shortint](#shortint) \| [int](#int) \| [longint](#longint) \| [integer](#integer) \| [time](#time)  
<a name="integer_vector_type"></a>integer\_vector\_type ::= [bit](#bit) \| [logic](#logic) \| [reg](#reg)  
<a name="non_integer_type"></a>non\_integer\_type ::= [shortreal](#shortreal) \| [real](#real) \| [realtime](#realtime)  
<a name="net_type"></a>net\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[supply0](#supply0) \| [supply1](#supply1) \| [tri](#tri) \| [triand](#triand) \| [trior](#trior) \| [trireg](#trireg) \| [tri0](#tri0) \| [tri1](#tri1) \| [uwire](#uwire) \| [wire](#wire) \| [wand](#wand) \| [wor](#wor)  
<a name="net_port_type"></a>net\_port\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [net_type](#net_type) ] [data_type_or_implicit](#data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nettype_identifier](#nettype_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interconnect](#interconnect) [implicit_data_type](#implicit_data_type)  
<a name="variable_port_type"></a>variable\_port\_type ::= [var_data_type](#var_data_type)  
<a name="var_data_type"></a>var\_data\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type](#data_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [var](#var) [data_type_or_implicit](#data_type_or_implicit)  
<a name="signing"></a>signing ::= [signed](#signed) \| [unsigned](#unsigned)  
<a name="simple_type"></a>simple\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integer_type](#integer_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [non_integer_type](#non_integer_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_type_identifier](#ps_type_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_parameter_identifier](#ps_parameter_identifier)  
<a name="struct_union"></a>struct\_union ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[struct](#struct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [union](#union) \[ [soft](#soft) \| [tagged](#tagged) ]  
<a name="struct_union_member20"></a>struct\_union\_member20 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } \[ [random_qualifier](#random_qualifier) ] [data_type_or_void](#data_type_or_void) [list_of_variable_decl_assignments](#list_of_variable_decl_assignments) `;`  
<a name="data_type_or_void"></a>data\_type\_or\_void ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type](#data_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [void](#void)  
<a name="type_reference"></a>type\_reference ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[type](#type) `(` [expression21](#expression21) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type](#type) `(` [data_type_or_incomplete_class_scoped_type](#data_type_or_incomplete_class_scoped_type) `)`  
<a name="data_type_or_incomplete_class_scoped_type"></a>data\_type\_or\_incomplete\_class\_scoped\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type](#data_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [incomplete_class_scoped_type](#incomplete_class_scoped_type)  
&nbsp;&nbsp;&nbsp;&nbsp;[incomplete_class_scoped_type](#incomplete_class_scoped_type) `::` `=`  
&nbsp;&nbsp;&nbsp;&nbsp;[type_identifier](#type_identifier) `::` [type_identifier_or_class_type](#type_identifier_or_class_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [incomplete_class_scoped_type](#incomplete_class_scoped_type) `::` [type_identifier_or_class_type](#type_identifier_or_class_type)  
<a name="type_identifier_or_class_type"></a>type\_identifier\_or\_class\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[type_identifier](#type_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_type](#class_type)  
#### A.2.2.2 Strengths
<a name="drive_strength"></a>drive\_strength ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [strength0](#strength0) `,` [strength1](#strength1) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength1](#strength1) `,` [strength0](#strength0) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength0](#strength0) `,` [highz1](#highz1) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength1](#strength1) `,` [highz0](#highz0) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [highz0](#highz0) `,` [strength1](#strength1) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [highz1](#highz1) `,` [strength0](#strength0) `)`  
<a name="strength0"></a>strength0 ::= [supply0](#supply0) \| [strong0](#strong0) \| [pull0](#pull0) \| [weak0](#weak0)  
<a name="strength1"></a>strength1 ::= [supply1](#supply1) \| [strong1](#strong1) \| [pull1](#pull1) \| [weak1](#weak1)  
<a name="charge_strength"></a>charge\_strength ::= `(` [small](#small) `)` \| `(` [medium](#medium) `)` \| `(` [large](#large) `)`  
#### A.2.2.3 Delays
<a name="delay2"></a>delay2 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`#` [delay_value](#delay_value)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `#` `(` [mintypmax_expression](#mintypmax_expression) \[ `,` [mintypmax_expression](#mintypmax_expression) ] `)`  
<a name="delay3"></a>delay3 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`#` [delay_value](#delay_value)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `#` `(` [mintypmax_expression](#mintypmax_expression) \[ `,` [mintypmax_expression](#mintypmax_expression) \[ `,` [mintypmax_expression](#mintypmax_expression) ] ] `)`  
<a name="delay_value"></a>delay\_value ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[unsigned_number](#unsigned_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [real_number](#real_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_identifier](#ps_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [time_literal](#time_literal)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [1step](#1step)  
### A.2.3 Declaration lists
<a name="list_of_defparam_assignments"></a>list\_of\_defparam\_assignments ::= [defparam_assignment](#defparam_assignment) \{ `,` [defparam_assignment](#defparam_assignment) }  
<a name="list_of_genvar_identifiers"></a>list\_of\_genvar\_identifiers ::= [genvar_identifier](#genvar_identifier) \{ `,` [genvar_identifier](#genvar_identifier) }  
<a name="list_of_interface_identifiers"></a>list\_of\_interface\_identifiers ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface_identifier](#interface_identifier) \{ [unpacked_dimension](#unpacked_dimension) } \{ `,` [interface_identifier](#interface_identifier) \{ [unpacked_dimension](#unpacked_dimension) } }  
<a name="list_of_net_decl_assignments"></a>list\_of\_net\_decl\_assignments ::= [net_decl_assignment](#net_decl_assignment) \{ `,` [net_decl_assignment](#net_decl_assignment) }  
<a name="list_of_param_assignments"></a>list\_of\_param\_assignments ::= [param_assignment](#param_assignment) \{ `,` [param_assignment](#param_assignment) }  
<a name="list_of_port_identifiers"></a>list\_of\_port\_identifiers ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_identifier](#port_identifier) \{ [unpacked_dimension](#unpacked_dimension) } \{ `,` [port_identifier](#port_identifier) \{ [unpacked_dimension](#unpacked_dimension) } }  
<a name="list_of_udp_port_identifiers"></a>list\_of\_udp\_port\_identifiers ::= [port_identifier](#port_identifier) \{ `,` [port_identifier](#port_identifier) }  
<a name="list_of_specparam_assignments"></a>list\_of\_specparam\_assignments ::= [specparam_assignment](#specparam_assignment) \{ `,` [specparam_assignment](#specparam_assignment) }  
<a name="list_of_tf_variable_identifiers"></a>list\_of\_tf\_variable\_identifiers ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\{ `,` [port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [expression](#expression) ] }  
<a name="list_of_type_assignments"></a>list\_of\_type\_assignments ::= [type_assignment](#type_assignment) \{ `,` [type_assignment](#type_assignment) }  
<a name="list_of_variable_decl_assignments"></a>list\_of\_variable\_decl\_assignments ::= [variable_decl_assignment](#variable_decl_assignment) \{ `,` [variable_decl_assignment](#variable_decl_assignment) }  
<a name="list_of_variable_identifiers"></a>list\_of\_variable\_identifiers ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[variable_identifier](#variable_identifier) \{ [variable_dimension](#variable_dimension) } \{ `,` [variable_identifier](#variable_identifier) \{ [variable_dimension](#variable_dimension) } }  
<a name="list_of_variable_port_identifiers"></a>list\_of\_variable\_port\_identifiers ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [constant_expression](#constant_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\{ `,` [port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [constant_expression](#constant_expression) ] }  
### A.2.4 Declaration assignments
<a name="defparam_assignment"></a>defparam\_assignment ::= [hierarchical_parameter_identifier](#hierarchical_parameter_identifier) `=` [constant_mintypmax_expression](#constant_mintypmax_expression)  
<a name="net_decl_assignment"></a>net\_decl\_assignment ::= [net_identifier](#net_identifier) \{ [unpacked_dimension](#unpacked_dimension) } \[ `=` [expression](#expression) ]  
<a name="param_assignment"></a>param\_assignment ::= [parameter_identifier](#parameter_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [constant_param_expression](#constant_param_expression) ][22](#22)  
<a name="specparam_assignment"></a>specparam\_assignment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[specparam_identifier](#specparam_identifier) `=` [constant_mintypmax_expression](#constant_mintypmax_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pulse_control_specparam](#pulse_control_specparam)  
<a name="pulse_control_specparam"></a>pulse\_control\_specparam ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[PATHPULSE](#PATHPULSE)`$` `=` `(` [reject_limit_value](#reject_limit_value) \[ `,` [error_limit_value](#error_limit_value) ] `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [PATHPULSE](#PATHPULSE)`$`[specify_input_terminal_descriptor](#specify_input_terminal_descriptor)`$`[specify_output_terminal_descriptor](#specify_output_terminal_descriptor)  
&nbsp;&nbsp;&nbsp;&nbsp;`=` `(` [reject_limit_value](#reject_limit_value) \[ `,` [error_limit_value](#error_limit_value) ] `)`  
<a name="error_limit_value"></a>error\_limit\_value ::= [limit_value](#limit_value)  
<a name="reject_limit_value"></a>reject\_limit\_value ::= [limit_value](#limit_value)  
<a name="limit_value"></a>limit\_value ::= [constant_mintypmax_expression](#constant_mintypmax_expression)  
<a name="type_assignment"></a>type\_assignment ::= [type_identifier](#type_identifier) \[ `=` [data_type_or_incomplete_class_scoped_type](#data_type_or_incomplete_class_scoped_type) ][22](#22)  
<a name="variable_decl_assignment"></a>variable\_decl\_assignment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[variable_identifier](#variable_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [dynamic_array_variable_identifier](#dynamic_array_variable_identifier) [unsized_dimension](#unsized_dimension) \{ [variable_dimension](#variable_dimension) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `=` [dynamic_array_new](#dynamic_array_new) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [class_variable_identifier](#class_variable_identifier) \[ `=` [class_new](#class_new) ]  
<a name="class_new23"></a>class\_new23 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [class_scope](#class_scope) ] [new](#new) \[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [new](#new) [expression](#expression)  
<a name="dynamic_array_new"></a>dynamic\_array\_new ::= [new](#new) \[ [expression](#expression) ] \[ `(` [expression](#expression) `)` ]  
### A.2.5 Declaration ranges
<a name="unpacked_dimension"></a>unpacked\_dimension ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [constant_range](#constant_range) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [constant_expression](#constant_expression) ]  
<a name="packed_dimension24"></a>packed\_dimension24 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [constant_range](#constant_range) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unsized_dimension](#unsized_dimension)  
<a name="associative_dimension"></a>associative\_dimension ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [data_type](#data_type) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ `*` ]  
<a name="variable_dimension"></a>variable\_dimension ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[unsized_dimension](#unsized_dimension)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unpacked_dimension](#unpacked_dimension)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [associative_dimension](#associative_dimension)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [queue_dimension](#queue_dimension)  
<a name="queue_dimension"></a>queue\_dimension ::= \[ `$` \[ `:` [constant_expression](#constant_expression) ] ]  
<a name="unsized_dimension"></a>unsized\_dimension ::= \[ ]  
### A.2.6 Function declarations
<a name="function_data_type_or_implicit"></a>function\_data\_type\_or\_implicit ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type_or_void](#data_type_or_void)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [implicit_data_type](#implicit_data_type)  
<a name="function_declaration"></a>function\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function](#function) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][25](#25) \[ [lifetime](#lifetime) ] [function_body_declaration](#function_body_declaration)  
<a name="function_body_declaration"></a>function\_body\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function_data_type_or_implicit](#function_data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [interface_identifier](#interface_identifier) `.` \| [class_scope](#class_scope) ] [function_identifier](#function_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [tf_item_declaration](#tf_item_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [function_statement_or_null](#function_statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endfunction](#endfunction) \[ `:` [function_identifier](#function_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_data_type_or_implicit](#function_data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [interface_identifier](#interface_identifier) `.` \| [class_scope](#class_scope) ] [function_identifier](#function_identifier) `(` \[ [tf_port_list](#tf_port_list) ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [block_item_declaration](#block_item_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [function_statement_or_null](#function_statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endfunction](#endfunction) \[ `:` [function_identifier](#function_identifier) ]  
<a name="function_prototype"></a>function\_prototype ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function](#function) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][25](#25) [data_type_or_void](#data_type_or_void) [function_identifier](#function_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `(` \[ [tf_port_list](#tf_port_list) ] `)` ]  
<a name="dpi_import_export"></a>dpi\_import\_export ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[import](#import) [dpi_spec_string](#dpi_spec_string) \[ [dpi_function_import_property](#dpi_function_import_property) ] \[ [c_identifier](#c_identifier) `=` ] [dpi_function_proto](#dpi_function_proto) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [import](#import) [dpi_spec_string](#dpi_spec_string) \[ [dpi_task_import_property](#dpi_task_import_property) ] \[ [c_identifier](#c_identifier) `=` ] [dpi_task_proto](#dpi_task_proto) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [export](#export) [dpi_spec_string](#dpi_spec_string) \[ [c_identifier](#c_identifier) `=` ] [function](#function) [function_identifier](#function_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [export](#export) [dpi_spec_string](#dpi_spec_string) \[ [c_identifier](#c_identifier) `=` ] [task](#task) [task_identifier](#task_identifier) `;`  
<a name="dpi_spec_string"></a>dpi\_spec\_string ::= `"`[DPI](#DPI)`-`[C](#C)`"` \| `"`[DPI](#DPI)`"`  
<a name="dpi_function_import_property"></a>dpi\_function\_import\_property ::= [context](#context) \| [pure](#pure)  
<a name="dpi_task_import_property"></a>dpi\_task\_import\_property ::= [context](#context)  
&nbsp;&nbsp;&nbsp;&nbsp;[dpi_function_proto26](#dpi_function_proto26)`,`  
<a name="27"></a>27 ::= [function_prototype](#function_prototype)  
<a name="dpi_task_proto27"></a>dpi\_task\_proto27 ::= [task_prototype](#task_prototype)  
### A.2.7 Task declarations
<a name="task_declaration"></a>task\_declaration ::= [task](#task) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][25](#25) \[ [lifetime](#lifetime) ] [task_body_declaration](#task_body_declaration)  
<a name="task_body_declaration"></a>task\_body\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [interface_identifier](#interface_identifier) `.` \| [class_scope](#class_scope) ] [task_identifier](#task_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [tf_item_declaration](#tf_item_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [statement_or_null](#statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endtask](#endtask) \[ `:` [task_identifier](#task_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [interface_identifier](#interface_identifier) `.` \| [class_scope](#class_scope) ] [task_identifier](#task_identifier) `(` \[ [tf_port_list](#tf_port_list) ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [block_item_declaration](#block_item_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [statement_or_null](#statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endtask](#endtask) \[ `:` [task_identifier](#task_identifier) ]  
<a name="tf_item_declaration"></a>tf\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[block_item_declaration](#block_item_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [tf_port_declaration](#tf_port_declaration)  
<a name="tf_port_list"></a>tf\_port\_list ::= [tf_port_item](#tf_port_item) \{ `,` [tf_port_item](#tf_port_item) }  
<a name="tf_port_item28"></a>tf\_port\_item28 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } \[ [tf_port_direction](#tf_port_direction) ] \[ [var](#var) ] [data_type_or_implicit](#data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [port_identifier](#port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [expression](#expression) ] ]  
<a name="tf_port_direction"></a>tf\_port\_direction ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_direction](#port_direction)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [const](#const) ] [ref](#ref) \[ [static](#static) ]  
<a name="tf_port_declaration"></a>tf\_port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [tf_port_direction](#tf_port_direction) \[ [var](#var) ] [data_type_or_implicit](#data_type_or_implicit) [list_of_tf_variable_identifiers](#list_of_tf_variable_identifiers) `;`  
<a name="task_prototype"></a>task\_prototype ::= [task](#task) \[ [dynamic_override_specifiers](#dynamic_override_specifiers) ][25](#25) [task_identifier](#task_identifier) \[ `(` \[ [tf_port_list](#tf_port_list) ] `)` ]  
<a name="dynamic_override_specifiers"></a>dynamic\_override\_specifiers ::= \[ [initial_or_extends_specifier](#initial_or_extends_specifier) ] \[ [final_specifier](#final_specifier) ]  
<a name="initial_or_extends_specifier"></a>initial\_or\_extends\_specifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`:` [initial](#initial)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `:` [extends](#extends)  
<a name="final_specifier"></a>final\_specifier ::= `:` [final](#final)  
### A.2.8 Block item declarations
<a name="block_item_declaration"></a>block\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [data_declaration](#data_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [local_parameter_declaration](#local_parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [parameter_declaration](#parameter_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [let_declaration](#let_declaration)  
### A.2.9 Interface declarations
<a name="modport_declaration"></a>modport\_declaration ::= [modport](#modport) [modport_item](#modport_item) \{ `,` [modport_item](#modport_item) } `;`  
<a name="modport_item"></a>modport\_item ::= [modport_identifier](#modport_identifier) `(` [modport_ports_declaration](#modport_ports_declaration) \{ `,` [modport_ports_declaration](#modport_ports_declaration) } `)`  
<a name="modport_ports_declaration"></a>modport\_ports\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [modport_simple_ports_declaration](#modport_simple_ports_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [modport_tf_ports_declaration](#modport_tf_ports_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [modport_clocking_declaration](#modport_clocking_declaration)  
<a name="modport_clocking_declaration"></a>modport\_clocking\_declaration ::= [clocking](#clocking) [clocking_identifier](#clocking_identifier)  
<a name="modport_simple_ports_declaration"></a>modport\_simple\_ports\_declaration ::= [port_direction](#port_direction) [modport_simple_port](#modport_simple_port) \{ `,` [modport_simple_port](#modport_simple_port) }  
<a name="modport_simple_port"></a>modport\_simple\_port ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[port_identifier](#port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [port_identifier](#port_identifier) `(` \[ [expression](#expression) ] `)`  
<a name="modport_tf_ports_declaration"></a>modport\_tf\_ports\_declaration ::= [import_export](#import_export) [modport_tf_port](#modport_tf_port) \{ `,` [modport_tf_port](#modport_tf_port) }  
<a name="modport_tf_port"></a>modport\_tf\_port ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[method_prototype](#method_prototype)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [tf_identifier](#tf_identifier)  
<a name="import_export"></a>import\_export ::= [import](#import) \| [export](#export)  
### A.2.10 Assertion declarations
<a name="concurrent_assertion_item"></a>concurrent\_assertion\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [block_identifier](#block_identifier) `:` ] [concurrent_assertion_statement](#concurrent_assertion_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_instantiation](#checker_instantiation)  
<a name="concurrent_assertion_statement"></a>concurrent\_assertion\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assert_property_statement](#assert_property_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assume_property_statement](#assume_property_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cover_property_statement](#cover_property_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cover_sequence_statement](#cover_sequence_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [restrict_property_statement](#restrict_property_statement)  
<a name="assert_property_statement"></a>assert\_property\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assert](#assert) [property](#property) `(` [property_spec](#property_spec) `)` [action_block](#action_block)  
<a name="assume_property_statement"></a>assume\_property\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assume](#assume) [property](#property) `(` [property_spec](#property_spec) `)` [action_block](#action_block)  
<a name="cover_property_statement"></a>cover\_property\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover](#cover) [property](#property) `(` [property_spec](#property_spec) `)` [statement_or_null](#statement_or_null)  
<a name="expect_property_statement"></a>expect\_property\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expect](#expect) `(` [property_spec](#property_spec) `)` [action_block](#action_block)  
<a name="cover_sequence_statement"></a>cover\_sequence\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover](#cover) [sequence](#sequence) `(` \[ [clocking_event](#clocking_event) ] \[ [disable](#disable) [iff](#iff) `(` [expression_or_dist](#expression_or_dist) `)` ] [sequence_expr](#sequence_expr) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;[statement_or_null](#statement_or_null)  
<a name="restrict_property_statement"></a>restrict\_property\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[restrict](#restrict) [property](#property) `(` [property_spec](#property_spec) `)` `;`  
<a name="property_instance"></a>property\_instance ::= [ps_or_hierarchical_property_identifier](#ps_or_hierarchical_property_identifier) \[ `(` \[ [property_list_of_arguments](#property_list_of_arguments) ] `)` ]  
<a name="property_list_of_arguments"></a>property\_list\_of\_arguments ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [property_actual_arg](#property_actual_arg) ] \{ `,` \[ [property_actual_arg](#property_actual_arg) ] } \{ `,` `.` [identifier](#identifier) `(` \[ [property_actual_arg](#property_actual_arg) ] `)` }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [identifier](#identifier) `(` \[ [property_actual_arg](#property_actual_arg) ] `)` \{ `,` `.` [identifier](#identifier) `(` \[ [property_actual_arg](#property_actual_arg) ] `)` }  
<a name="property_actual_arg"></a>property\_actual\_arg ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_actual_arg](#sequence_actual_arg)  
<a name="assertion_item_declaration"></a>assertion\_item\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[property_declaration](#property_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_declaration](#sequence_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [let_declaration](#let_declaration)  
<a name="property_declaration"></a>property\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[property](#property) [property_identifier](#property_identifier) \[ `(` \[ [property_port_list](#property_port_list) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [assertion_variable_declaration](#assertion_variable_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;[property_spec](#property_spec) \[ `;` ]  
&nbsp;&nbsp;&nbsp;&nbsp;[endproperty](#endproperty) \[ `:` [property_identifier](#property_identifier) ]  
<a name="property_port_list"></a>property\_port\_list ::= [property_port_item](#property_port_item) \{ `,` [property_port_item](#property_port_item) }  
<a name="property_port_item"></a>property\_port\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } \[ [local](#local) \[ [property_lvar_port_direction](#property_lvar_port_direction) ] ] [property_formal_type](#property_formal_type)  
&nbsp;&nbsp;&nbsp;&nbsp;[formal_port_identifier](#formal_port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [property_actual_arg](#property_actual_arg) ]  
<a name="property_lvar_port_direction"></a>property\_lvar\_port\_direction ::= [input](#input)  
<a name="property_formal_type"></a>property\_formal\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[sequence_formal_type](#sequence_formal_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property](#property)  
<a name="property_spec"></a>property\_spec ::= \[ [clocking_event](#clocking_event) ] \[ [disable](#disable) [iff](#iff) `(` [expression_or_dist](#expression_or_dist) `)` ] [property_expr](#property_expr)  
<a name="property_expr"></a>property\_expr ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [strong](#strong) `(` [sequence_expr](#sequence_expr) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [weak](#weak) `(` [sequence_expr](#sequence_expr) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [property_expr](#property_expr) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [not](#not) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [or](#or) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [and](#and) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) `|->` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) `|=>` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [if](#if) `(` [expression_or_dist](#expression_or_dist) `)` [property_expr](#property_expr) \[ [else](#else) [property_expr](#property_expr) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [case](#case) `(` [expression_or_dist](#expression_or_dist) `)` [property_case_item](#property_case_item) \{ [property_case_item](#property_case_item) } [endcase](#endcase)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) `#-#` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) `#=#` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nexttime](#nexttime) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nexttime](#nexttime) \[ [constant_expression](#constant_expression) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [s_nexttime](#s_nexttime) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [s_nexttime](#s_nexttime) \[ [constant_expression](#constant_expression) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [always](#always) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [always](#always) \[ [cycle_delay_const_range_expression](#cycle_delay_const_range_expression) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [s_always](#s_always) \[ [constant_range](#constant_range) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [s_eventually](#s_eventually) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [eventually](#eventually) \[ [constant_range](#constant_range) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [s_eventually](#s_eventually) \[ [cycle_delay_const_range_expression](#cycle_delay_const_range_expression) ] [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [until](#until) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [s_until](#s_until) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [until_with](#until_with) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [s_until_with](#s_until_with) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [implies](#implies) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_expr](#property_expr) [iff](#iff) [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [accept_on](#accept_on) `(` [expression_or_dist](#expression_or_dist) `)` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [reject_on](#reject_on) `(` [expression_or_dist](#expression_or_dist) `)` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sync_accept_on](#sync_accept_on) `(` [expression_or_dist](#expression_or_dist) `)` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sync_reject_on](#sync_reject_on) `(` [expression_or_dist](#expression_or_dist) `)` [property_expr](#property_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [property_instance](#property_instance)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_event](#clocking_event) [property_expr](#property_expr)  
<a name="property_case_item"></a>property\_case\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression_or_dist](#expression_or_dist) \{ `,` [expression_or_dist](#expression_or_dist) } `:` [property_expr](#property_expr) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [property_expr](#property_expr) `;`  
<a name="sequence_declaration"></a>sequence\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[sequence](#sequence) [sequence_identifier](#sequence_identifier) \[ `(` \[ [sequence_port_list](#sequence_port_list) ] `)` ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [assertion_variable_declaration](#assertion_variable_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;[sequence_expr](#sequence_expr) \[ `;` ]  
&nbsp;&nbsp;&nbsp;&nbsp;[endsequence](#endsequence) \[ `:` [sequence_identifier](#sequence_identifier) ]  
<a name="sequence_port_list"></a>sequence\_port\_list ::= [sequence_port_item](#sequence_port_item) \{ `,` [sequence_port_item](#sequence_port_item) }  
<a name="sequence_port_item"></a>sequence\_port\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } \[ [local](#local) \[ [sequence_lvar_port_direction](#sequence_lvar_port_direction) ] ] [sequence_formal_type](#sequence_formal_type)  
&nbsp;&nbsp;&nbsp;&nbsp;[formal_port_identifier](#formal_port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [sequence_actual_arg](#sequence_actual_arg) ]  
<a name="sequence_lvar_port_direction"></a>sequence\_lvar\_port\_direction ::= [input](#input) \| [inout](#inout) \| [output](#output)  
<a name="sequence_formal_type"></a>sequence\_formal\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type_or_implicit](#data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence](#sequence)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [untyped](#untyped)  
<a name="sequence_expr"></a>sequence\_expr ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cycle_delay_range](#cycle_delay_range) [sequence_expr](#sequence_expr) \{ [cycle_delay_range](#cycle_delay_range) [sequence_expr](#sequence_expr) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) [cycle_delay_range](#cycle_delay_range) [sequence_expr](#sequence_expr) \{ [cycle_delay_range](#cycle_delay_range) [sequence_expr](#sequence_expr) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression_or_dist](#expression_or_dist) \[ [boolean_abbrev](#boolean_abbrev) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_instance](#sequence_instance) \[ [sequence_abbrev](#sequence_abbrev) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [sequence_expr](#sequence_expr) \{ `,` [sequence_match_item](#sequence_match_item) } `)` \[ [sequence_abbrev](#sequence_abbrev) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) [and](#and) [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) [intersect](#intersect) [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) [or](#or) [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [first_match](#first_match) `(` [sequence_expr](#sequence_expr) \{ `,` [sequence_match_item](#sequence_match_item) } `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression_or_dist](#expression_or_dist) [throughout](#throughout) [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr) [within](#within) [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_event](#clocking_event) [sequence_expr](#sequence_expr)  
<a name="cycle_delay_range"></a>cycle\_delay\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`##` [constant_primary](#constant_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `##` \[ [cycle_delay_const_range_expression](#cycle_delay_const_range_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| `##[*]`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `##[+]`  
<a name="sequence_method_call"></a>sequence\_method\_call ::= [sequence_instance](#sequence_instance) `.` [method_identifier](#method_identifier)  
<a name="sequence_match_item"></a>sequence\_match\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[operator_assignment](#operator_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inc_or_dec_expression](#inc_or_dec_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [subroutine_call](#subroutine_call)  
<a name="sequence_instance"></a>sequence\_instance ::= [ps_or_hierarchical_sequence_identifier](#ps_or_hierarchical_sequence_identifier) \[ `(` \[ [sequence_list_of_arguments](#sequence_list_of_arguments) ] `)` ]  
<a name="sequence_list_of_arguments"></a>sequence\_list\_of\_arguments ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [sequence_actual_arg](#sequence_actual_arg) ] \{ `,` \[ [sequence_actual_arg](#sequence_actual_arg) ] } \{ `,` `.` [identifier](#identifier) `(` \[ [sequence_actual_arg](#sequence_actual_arg) ] `)` }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [identifier](#identifier) `(` \[ [sequence_actual_arg](#sequence_actual_arg) ] `)` \{ `,` `.` [identifier](#identifier) `(` \[ [sequence_actual_arg](#sequence_actual_arg) ] `)` }  
<a name="sequence_actual_arg"></a>sequence\_actual\_arg ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[event_expression](#event_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_expr](#sequence_expr)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`  
<a name="boolean_abbrev"></a>boolean\_abbrev ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[consecutive_repetition](#consecutive_repetition)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nonconsecutive_repetition](#nonconsecutive_repetition)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [goto_repetition](#goto_repetition)  
<a name="sequence_abbrev"></a>sequence\_abbrev ::= [consecutive_repetition](#consecutive_repetition)  
<a name="consecutive_repetition"></a>consecutive\_repetition ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`[*` [const_or_range_expression](#const_or_range_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| `[*]`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `[+]`  
<a name="nonconsecutive_repetition"></a>nonconsecutive\_repetition ::= `[=` [const_or_range_expression](#const_or_range_expression) ]  
<a name="goto_repetition"></a>goto\_repetition ::= `[->` [const_or_range_expression](#const_or_range_expression) ]  
<a name="const_or_range_expression"></a>const\_or\_range\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cycle_delay_const_range_expression](#cycle_delay_const_range_expression)  
<a name="cycle_delay_const_range_expression"></a>cycle\_delay\_const\_range\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_expression](#constant_expression) `:` [constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression) `:` `$`  
<a name="assertion_variable_declaration"></a>assertion\_variable\_declaration ::= [var_data_type](#var_data_type) [list_of_variable_decl_assignments](#list_of_variable_decl_assignments) `;`  
### A.2.11 Covergroup declarations
<a name="covergroup_declaration"></a>covergroup\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[covergroup](#covergroup) [covergroup_identifier](#covergroup_identifier) \[ `(` \[ [tf_port_list](#tf_port_list) ] `)` ] \[ [coverage_event](#coverage_event) ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [coverage_spec_or_option](#coverage_spec_or_option) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endgroup](#endgroup) \[ `:` [covergroup_identifier](#covergroup_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [covergroup](#covergroup) [extends](#extends) [covergroup_identifier](#covergroup_identifier) `;`[29](#29)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [coverage_spec_or_option](#coverage_spec_or_option) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endgroup](#endgroup) \[ `:` [covergroup_identifier](#covergroup_identifier) ]  
<a name="coverage_spec_or_option"></a>coverage\_spec\_or\_option ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [coverage_spec](#coverage_spec)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [coverage_option](#coverage_option) `;`  
<a name="coverage_option"></a>coverage\_option ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[option](#option) `.` [member_identifier](#member_identifier) `=` [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_option](#type_option) `.` [member_identifier](#member_identifier) `=` [constant_expression](#constant_expression)  
<a name="coverage_spec"></a>coverage\_spec ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover_point](#cover_point)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cover_cross](#cover_cross)  
<a name="coverage_event"></a>coverage\_event ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[clocking_event](#clocking_event)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [with](#with) [function](#function) [sample](#sample) `(` \[ [tf_port_list](#tf_port_list) ] `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `@@` `(` [block_event_expression](#block_event_expression) `)`  
<a name="block_event_expression"></a>block\_event\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[block_event_expression](#block_event_expression) [or](#or) [block_event_expression](#block_event_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [begin](#begin) [hierarchical_btf_identifier](#hierarchical_btf_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [end](#end) [hierarchical_btf_identifier](#hierarchical_btf_identifier)  
<a name="hierarchical_btf_identifier"></a>hierarchical\_btf\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[hierarchical_tf_identifier](#hierarchical_tf_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hierarchical_block_identifier](#hierarchical_block_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [hierarchical_identifier](#hierarchical_identifier) `.` \| [class_scope](#class_scope) ] [method_identifier](#method_identifier)  
<a name="cover_point"></a>cover\_point ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ \[ [data_type_or_implicit](#data_type_or_implicit) ] [cover_point_identifier](#cover_point_identifier) `:` ] [coverpoint](#coverpoint) [expression](#expression) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;[bins_or_empty](#bins_or_empty)  
<a name="bins_or_empty"></a>bins\_or\_empty ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ \{ [attribute_instance](#attribute_instance) } \{ [bins_or_options](#bins_or_options) `;` } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="bins_or_options"></a>bins\_or\_options ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[coverage_option](#coverage_option)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [wildcard](#wildcard) ] [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) \[ \[ \[ [covergroup_expression](#covergroup_expression) ] ] ] `=`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [covergroup_range_list](#covergroup_range_list) } \[ [with](#with) `(` [with_covergroup_expression](#with_covergroup_expression) `)` ] \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [wildcard](#wildcard) ] [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) \[ \[ \[ [covergroup_expression](#covergroup_expression) ] ] ] `=`  
&nbsp;&nbsp;&nbsp;&nbsp;[cover_point_identifier](#cover_point_identifier) [with](#with) `(` [with_covergroup_expression](#with_covergroup_expression) `)` \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [wildcard](#wildcard) ] [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) \[ \[ \[ [covergroup_expression](#covergroup_expression) ] ] ] `=`  
&nbsp;&nbsp;&nbsp;&nbsp;[set_covergroup_expression](#set_covergroup_expression) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [wildcard](#wildcard)] [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) \[ \[ ] ] `=` [trans_list](#trans_list) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) \[ \[ \[ [covergroup_expression](#covergroup_expression) ] ] ] `=` [default](#default) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) `=` [default](#default) [sequence](#sequence) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;[bins_keyword](#bins_keyword)`::=` [bins](#bins) \| [illegal_bins](#illegal_bins) \| [ignore_bins](#ignore_bins)  
<a name="trans_list"></a>trans\_list ::= `(` [trans_set](#trans_set) `)` \{ `,` `(` [trans_set](#trans_set) `)` }  
<a name="trans_set"></a>trans\_set ::= [trans_range_list](#trans_range_list) \{ `=>` [trans_range_list](#trans_range_list) }  
<a name="trans_range_list"></a>trans\_range\_list ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[trans_item](#trans_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [trans_item](#trans_item) `[*` [repeat_range](#repeat_range) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [trans_item](#trans_item) \[[â](#â)`€“>` [repeat_range](#repeat_range) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [trans_item](#trans_item) `[=` [repeat_range](#repeat_range) ]  
<a name="trans_item"></a>trans\_item ::= [covergroup_range_list](#covergroup_range_list)  
<a name="repeat_range"></a>repeat\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[covergroup_expression](#covergroup_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [covergroup_expression](#covergroup_expression) `:` [covergroup_expression](#covergroup_expression)  
<a name="cover_cross"></a>cover\_cross ::= \[ [cross_identifier](#cross_identifier) `:` ] [cross](#cross) [list_of_cross_items](#list_of_cross_items) \[ [iff](#iff) `(` [expression](#expression) `)` ] [cross_body](#cross_body)  
<a name="list_of_cross_items"></a>list\_of\_cross\_items ::= [cross_item](#cross_item) `,` [cross_item](#cross_item) \{ `,` [cross_item](#cross_item) }  
<a name="cross_item"></a>cross\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover_point_identifier](#cover_point_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [variable_identifier](#variable_identifier)  
<a name="cross_body"></a>cross\_body ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ \{ [cross_body_item](#cross_body_item) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `;`  
<a name="cross_body_item"></a>cross\_body\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function_declaration](#function_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [bins_selection_or_option](#bins_selection_or_option) `;`  
<a name="bins_selection_or_option"></a>bins\_selection\_or\_option ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [coverage_option](#coverage_option)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [bins_selection](#bins_selection)  
<a name="bins_selection"></a>bins\_selection ::= [bins_keyword](#bins_keyword) [bin_identifier](#bin_identifier) `=` [select_expression](#select_expression) \[ [iff](#iff) `(` [expression](#expression) `)` ]  
<a name="select_expression30"></a>select\_expression30 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[select_condition](#select_condition)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `!` [select_condition](#select_condition)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [select_expression](#select_expression) `&&` [select_expression](#select_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [select_expression](#select_expression) `||` [select_expression](#select_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [select_expression](#select_expression) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [select_expression](#select_expression) [with](#with) `(` [with_covergroup_expression](#with_covergroup_expression) `)` \[ [matches](#matches) [integer_covergroup_expression](#integer_covergroup_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cross_identifier](#cross_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cross_set_expression](#cross_set_expression) \[ [matches](#matches) [integer_covergroup_expression](#integer_covergroup_expression) ]  
<a name="select_condition"></a>select\_condition ::= [binsof](#binsof) `(` [bins_expression](#bins_expression) `)` \[ [intersect](#intersect) \{ [covergroup_range_list](#covergroup_range_list) } ]  
<a name="bins_expression"></a>bins\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[variable_identifier](#variable_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cover_point_identifier](#cover_point_identifier) \[ `.` [bin_identifier](#bin_identifier) ]  
<a name="covergroup_range_list"></a>covergroup\_range\_list ::= [covergroup_value_range](#covergroup_value_range) \{ `,` [covergroup_value_range](#covergroup_value_range) }  
<a name="covergroup_value_range"></a>covergroup\_value\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[covergroup_expression](#covergroup_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [covergroup_expression](#covergroup_expression) `:` [covergroup_expression](#covergroup_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ `$` `:` [covergroup_expression](#covergroup_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [covergroup_expression](#covergroup_expression) `:` `$` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [covergroup_expression](#covergroup_expression) `+/-` [covergroup_expression](#covergroup_expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [covergroup_expression](#covergroup_expression) `+%-` [covergroup_expression](#covergroup_expression) ]  
<a name="with_covergroup_expression"></a>with\_covergroup\_expression ::= [covergroup_expression31](#covergroup_expression31)  
<a name="set_covergroup_expression"></a>set\_covergroup\_expression ::= [covergroup_expression32](#covergroup_expression32)  
<a name="integer_covergroup_expression"></a>integer\_covergroup\_expression ::= [covergroup_expression](#covergroup_expression) \|  `$`  
<a name="cross_set_expression"></a>cross\_set\_expression ::= [covergroup_expression](#covergroup_expression)  
<a name="covergroup_expression"></a>covergroup\_expression ::= [expression33](#expression33)  
### A.2.12 Let declarations
<a name="let_declaration"></a>let\_declaration ::= [let](#let) [let_identifier](#let_identifier) \[ `(` \[ [let_port_list](#let_port_list) ] `)` ] `=` [expression](#expression) `;`  
<a name="let_identifier"></a>let\_identifier ::= [identifier](#identifier)  
<a name="let_port_list"></a>let\_port\_list ::= [let_port_item](#let_port_item) \{ `,` [let_port_item](#let_port_item) }  
<a name="let_port_item"></a>let\_port\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [let_formal_type](#let_formal_type) [formal_port_identifier](#formal_port_identifier) \{ [variable_dimension](#variable_dimension) } \[ `=` [expression](#expression) ]  
<a name="let_formal_type"></a>let\_formal\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[data_type_or_implicit](#data_type_or_implicit)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [untyped](#untyped)  
<a name="let_expression"></a>let\_expression ::= \[ [package_scope](#package_scope) ] [let_identifier](#let_identifier) \[ `(` \[ [let_list_of_arguments](#let_list_of_arguments) ] `)` ]  
<a name="let_list_of_arguments"></a>let\_list\_of\_arguments ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [let_actual_arg](#let_actual_arg) ] \{ `,` \[ [let_actual_arg](#let_actual_arg) ] } \{ `,` `.` [identifier](#identifier) `(` \[ [let_actual_arg](#let_actual_arg) ] `)` }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [identifier](#identifier) `(` \[ [let_actual_arg](#let_actual_arg) ] `)` \{ `,` `.` [identifier](#identifier) `(` \[ [let_actual_arg](#let_actual_arg) ] `)` }  
<a name="let_actual_arg"></a>let\_actual\_arg ::= [expression](#expression)  
## A.3 Primitive instances
### A.3.1 Primitive instantiation and instances
<a name="gate_instantiation"></a>gate\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cmos_switchtype](#cmos_switchtype) \[ [delay3](#delay3) ] [cmos_switch_instance](#cmos_switch_instance) \{ `,` [cmos_switch_instance](#cmos_switch_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [mos_switchtype](#mos_switchtype) \[ [delay3](#delay3) ] [mos_switch_instance](#mos_switch_instance) \{ `,` [mos_switch_instance](#mos_switch_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [enable_gatetype](#enable_gatetype) \[ [drive_strength](#drive_strength) ] \[ [delay3](#delay3) ] [enable_gate_instance](#enable_gate_instance) \{ `,` [enable_gate_instance](#enable_gate_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [n_input_gatetype](#n_input_gatetype) \[ [drive_strength](#drive_strength) ] \[ [delay2](#delay2) ] [n_input_gate_instance](#n_input_gate_instance) \{ `,` [n_input_gate_instance](#n_input_gate_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [n_output_gatetype](#n_output_gatetype) \[ [drive_strength](#drive_strength) ] \[ [delay2](#delay2) ] [n_output_gate_instance](#n_output_gate_instance) \{ `,` [n_output_gate_instance](#n_output_gate_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pass_en_switchtype](#pass_en_switchtype) \[ [delay2](#delay2) ] [pass_enable_switch_instance](#pass_enable_switch_instance) \{ `,` [pass_enable_switch_instance](#pass_enable_switch_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pass_switchtype](#pass_switchtype) [pass_switch_instance](#pass_switch_instance) \{ `,` [pass_switch_instance](#pass_switch_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pulldown](#pulldown) \[ [pulldown_strength](#pulldown_strength) ] [pull_gate_instance](#pull_gate_instance) \{ `,` [pull_gate_instance](#pull_gate_instance) } `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pullup](#pullup) \[ [pullup_strength](#pullup_strength) ] [pull_gate_instance](#pull_gate_instance) \{ `,` [pull_gate_instance](#pull_gate_instance) } `;`  
<a name="cmos_switch_instance"></a>cmos\_switch\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `,` [input_terminal](#input_terminal) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[ncontrol_terminal](#ncontrol_terminal) `,` [pcontrol_terminal](#pcontrol_terminal) `)`  
<a name="enable_gate_instance"></a>enable\_gate\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `,` [input_terminal](#input_terminal) `,` [enable_terminal](#enable_terminal) `)`  
<a name="mos_switch_instance"></a>mos\_switch\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `,` [input_terminal](#input_terminal) `,` [enable_terminal](#enable_terminal) `)`  
<a name="n_input_gate_instance"></a>n\_input\_gate\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `,` [input_terminal](#input_terminal) \{ `,` [input_terminal](#input_terminal) } `)`  
<a name="n_output_gate_instance"></a>n\_output\_gate\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) \{ `,` [output_terminal](#output_terminal) } `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[input_terminal](#input_terminal) `)`  
<a name="pass_switch_instance"></a>pass\_switch\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [inout_terminal](#inout_terminal) `,` [inout_terminal](#inout_terminal) `)`  
<a name="pass_enable_switch_instance"></a>pass\_enable\_switch\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [inout_terminal](#inout_terminal) `,` [inout_terminal](#inout_terminal) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[enable_terminal](#enable_terminal) `)`  
<a name="pull_gate_instance"></a>pull\_gate\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `)`  
### A.3.2 Primitive strengths
<a name="pulldown_strength"></a>pulldown\_strength ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [strength0](#strength0) `,` [strength1](#strength1) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength1](#strength1) `,` [strength0](#strength0) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength0](#strength0) `)`  
<a name="pullup_strength"></a>pullup\_strength ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [strength0](#strength0) `,` [strength1](#strength1) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength1](#strength1) `,` [strength0](#strength0) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [strength1](#strength1) `)`  
### A.3.3 Primitive terminals
<a name="enable_terminal"></a>enable\_terminal ::= [expression](#expression)  
<a name="inout_terminal"></a>inout\_terminal ::= [net_lvalue](#net_lvalue)  
<a name="input_terminal"></a>input\_terminal ::= [expression](#expression)  
<a name="ncontrol_terminal"></a>ncontrol\_terminal ::= [expression](#expression)  
<a name="output_terminal"></a>output\_terminal ::= [net_lvalue](#net_lvalue)  
<a name="pcontrol_terminal"></a>pcontrol\_terminal ::= [expression](#expression)  
### A.3.4 Primitive gate and switch types
<a name="cmos_switchtype"></a>cmos\_switchtype ::= [cmos](#cmos) \| [rcmos](#rcmos)  
<a name="enable_gatetype"></a>enable\_gatetype ::= [bufif0](#bufif0) \| [bufif1](#bufif1) \| [notif0](#notif0) \| [notif1](#notif1)  
<a name="mos_switchtype"></a>mos\_switchtype ::= [nmos](#nmos) \| [pmos](#pmos) \| [rnmos](#rnmos) \| [rpmos](#rpmos)  
<a name="n_input_gatetype"></a>n\_input\_gatetype ::= [and](#and) \| [nand](#nand) \| [or](#or) \| [nor](#nor) \| [xor](#xor) \| [xnor](#xnor)  
<a name="n_output_gatetype"></a>n\_output\_gatetype ::= [buf](#buf) \| [not](#not)  
<a name="pass_en_switchtype"></a>pass\_en\_switchtype ::= [tranif0](#tranif0) \| [tranif1](#tranif1) \| [rtranif1](#rtranif1) \| [rtranif0](#rtranif0)  
<a name="pass_switchtype"></a>pass\_switchtype ::= [tran](#tran) \| [rtran](#rtran)  
## A.4 Instantiations
### A.4.1 Instantiation
#### A.4.1.1 Module instantiation
<a name="module_instantiation"></a>module\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_identifier](#module_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ] [hierarchical_instance](#hierarchical_instance) \{ `,` [hierarchical_instance](#hierarchical_instance) } `;`  
<a name="parameter_value_assignment"></a>parameter\_value\_assignment ::= `#` `(` \[ [list_of_parameter_value_assignments](#list_of_parameter_value_assignments) ] `)`  
<a name="list_of_parameter_value_assignments"></a>list\_of\_parameter\_value\_assignments ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ordered_parameter_assignment](#ordered_parameter_assignment) \{ `,` [ordered_parameter_assignment](#ordered_parameter_assignment) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [named_parameter_assignment](#named_parameter_assignment) \{ `,` [named_parameter_assignment](#named_parameter_assignment) }  
<a name="ordered_parameter_assignment"></a>ordered\_parameter\_assignment ::= [param_expression](#param_expression)  
<a name="named_parameter_assignment"></a>named\_parameter\_assignment ::= `.` [parameter_identifier](#parameter_identifier) `(` \[ [param_expression](#param_expression) ] `)`  
<a name="hierarchical_instance"></a>hierarchical\_instance ::= [name_of_instance](#name_of_instance) `(` \[ [list_of_port_connections](#list_of_port_connections) ] `)`  
<a name="name_of_instance"></a>name\_of\_instance ::= [instance_identifier](#instance_identifier) \{ [unpacked_dimension](#unpacked_dimension) }  
<a name="list_of_port_connections34"></a>list\_of\_port\_connections34 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ordered_port_connection](#ordered_port_connection) \{ `,` [ordered_port_connection](#ordered_port_connection) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [named_port_connection](#named_port_connection) \{ `,` [named_port_connection](#named_port_connection) }  
<a name="ordered_port_connection"></a>ordered\_port\_connection ::= \{ [attribute_instance](#attribute_instance) } \[ [expression](#expression) ]  
<a name="named_port_connection"></a>named\_port\_connection ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } `.` [port_identifier](#port_identifier) \[ `(` \[ [expression](#expression) ] `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } `.` `*`  
#### A.4.1.2 Interface instantiation
<a name="interface_instantiation"></a>interface\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[interface_identifier](#interface_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ] [hierarchical_instance](#hierarchical_instance) \{ `,` [hierarchical_instance](#hierarchical_instance) } `;`  
#### A.4.1.3 Program instantiation
<a name="program_instantiation"></a>program\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[program_identifier](#program_identifier) \[ [parameter_value_assignment](#parameter_value_assignment) ] [hierarchical_instance](#hierarchical_instance) \{ `,` [hierarchical_instance](#hierarchical_instance) } `;`  
#### A.4.1.4 Checker instantiation
<a name="checker_instantiation"></a>checker\_instantiation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ps_checker_identifier](#ps_checker_identifier) [name_of_instance](#name_of_instance) `(` \[ [list_of_checker_port_connections](#list_of_checker_port_connections) ] `)` `;`  
<a name="list_of_checker_port_connections34"></a>list\_of\_checker\_port\_connections34 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ordered_checker_port_connection](#ordered_checker_port_connection) \{ `,` [ordered_checker_port_connection](#ordered_checker_port_connection) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [named_checker_port_connection](#named_checker_port_connection) \{ `,` [named_checker_port_connection](#named_checker_port_connection) }  
<a name="ordered_checker_port_connection"></a>ordered\_checker\_port\_connection ::= \{ [attribute_instance](#attribute_instance) } \[ [property_actual_arg](#property_actual_arg) ]  
<a name="named_checker_port_connection"></a>named\_checker\_port\_connection ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } `.` [formal_port_identifier](#formal_port_identifier) \[ `(` \[ [property_actual_arg](#property_actual_arg) ] `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } `.` `*`  
### A.4.2 Generated instantiation
<a name="generate_region"></a>generate\_region ::= [generate](#generate) \{ [generate_item](#generate_item) } [endgenerate](#endgenerate)  
<a name="loop_generate_construct"></a>loop\_generate\_construct ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[for](#for) `(` [genvar_initialization](#genvar_initialization) `;` [genvar_expression](#genvar_expression) `;` [genvar_iteration](#genvar_iteration) `)` [generate_block](#generate_block)  
<a name="genvar_initialization"></a>genvar\_initialization ::= \[ [genvar](#genvar) ] [genvar_identifier](#genvar_identifier) `=` [constant_expression](#constant_expression)  
<a name="genvar_iteration"></a>genvar\_iteration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[genvar_identifier](#genvar_identifier) [assignment_operator](#assignment_operator) [genvar_expression](#genvar_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inc_or_dec_operator](#inc_or_dec_operator) [genvar_identifier](#genvar_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [genvar_identifier](#genvar_identifier) [inc_or_dec_operator](#inc_or_dec_operator)  
<a name="conditional_generate_construct"></a>conditional\_generate\_construct ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[if_generate_construct](#if_generate_construct)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [case_generate_construct](#case_generate_construct)  
<a name="if_generate_construct"></a>if\_generate\_construct ::= [if](#if) `(` [constant_expression](#constant_expression) `)` [generate_block](#generate_block) \[ [else](#else) [generate_block](#generate_block) ]  
<a name="case_generate_construct"></a>case\_generate\_construct ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[case](#case) `(` [constant_expression](#constant_expression) `)` [case_generate_item](#case_generate_item) \{ [case_generate_item](#case_generate_item) } [endcase](#endcase)  
<a name="case_generate_item"></a>case\_generate\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_expression](#constant_expression) \{ `,` [constant_expression](#constant_expression) } `:` [generate_block](#generate_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [generate_block](#generate_block)  
<a name="generate_block"></a>generate\_block ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[generate_item](#generate_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [generate_block_identifier](#generate_block_identifier) `:` ] [begin](#begin) \[ `:` [generate_block_identifier](#generate_block_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [generate_item](#generate_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[end](#end) \[ `:` [generate_block_identifier](#generate_block_identifier) ]  
<a name="generate_item35"></a>generate\_item35 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_or_generate_item](#module_or_generate_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_or_generate_item](#interface_or_generate_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_or_generate_item](#checker_or_generate_item)  
## A.5 UDP declaration and instantiation
### A.5.1 UDP declaration
<a name="udp_nonansi_declaration"></a>udp\_nonansi\_declaration ::= \{ [attribute_instance](#attribute_instance) } [primitive](#primitive) [udp_identifier](#udp_identifier) `(` [udp_port_list](#udp_port_list) `)` `;`  
<a name="udp_ansi_declaration"></a>udp\_ansi\_declaration ::= \{ [attribute_instance](#attribute_instance) } [primitive](#primitive) [udp_identifier](#udp_identifier) `(` [udp_declaration_port_list](#udp_declaration_port_list) `)` `;`  
<a name="udp_declaration"></a>udp\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[udp_nonansi_declaration](#udp_nonansi_declaration) [udp_port_declaration](#udp_port_declaration) \{ [udp_port_declaration](#udp_port_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;[udp_body](#udp_body)  
&nbsp;&nbsp;&nbsp;&nbsp;[endprimitive](#endprimitive) \[ `:` [udp_identifier](#udp_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [udp_ansi_declaration](#udp_ansi_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;[udp_body](#udp_body)  
&nbsp;&nbsp;&nbsp;&nbsp;[endprimitive](#endprimitive) \[ `:` [udp_identifier](#udp_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [udp_nonansi_declaration](#udp_nonansi_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [extern](#extern) [udp_ansi_declaration](#udp_ansi_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [primitive](#primitive) [udp_identifier](#udp_identifier) `(` `.` `*` `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [udp_port_declaration](#udp_port_declaration) }  
&nbsp;&nbsp;&nbsp;&nbsp;[udp_body](#udp_body)  
&nbsp;&nbsp;&nbsp;&nbsp;[endprimitive](#endprimitive) \[ `:` [udp_identifier](#udp_identifier) ]  
### A.5.2 UDP ports
<a name="udp_port_list"></a>udp\_port\_list ::= [output_port_identifier](#output_port_identifier) `,` [input_port_identifier](#input_port_identifier) \{ `,` [input_port_identifier](#input_port_identifier) }  
<a name="udp_declaration_port_list"></a>udp\_declaration\_port\_list ::= [udp_output_declaration](#udp_output_declaration) `,` [udp_input_declaration](#udp_input_declaration) \{ `,` [udp_input_declaration](#udp_input_declaration) }  
<a name="udp_port_declaration"></a>udp\_port\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[udp_output_declaration](#udp_output_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [udp_input_declaration](#udp_input_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [udp_reg_declaration](#udp_reg_declaration) `;`  
<a name="udp_output_declaration"></a>udp\_output\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [attribute_instance](#attribute_instance) } [output](#output) [port_identifier](#port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [output](#output) [reg](#reg) [port_identifier](#port_identifier) \[ `=` [constant_expression](#constant_expression) ]  
<a name="udp_input_declaration"></a>udp\_input\_declaration ::= \{ [attribute_instance](#attribute_instance) } [input](#input) [list_of_udp_port_identifiers](#list_of_udp_port_identifiers)  
<a name="udp_reg_declaration"></a>udp\_reg\_declaration ::= \{ [attribute_instance](#attribute_instance) } [reg](#reg) [variable_identifier](#variable_identifier)  
### A.5.3 UDP body
<a name="udp_body"></a>udp\_body ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[combinational_body](#combinational_body)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequential_body](#sequential_body)  
<a name="combinational_body"></a>combinational\_body ::= [table](#table) [combinational_entry](#combinational_entry) \{ [combinational_entry](#combinational_entry) } [endtable](#endtable)  
<a name="combinational_entry"></a>combinational\_entry ::= [level_input_list](#level_input_list) `:` [output_symbol](#output_symbol) `;`  
<a name="sequential_body"></a>sequential\_body ::= \[ [udp_initial_statement](#udp_initial_statement) ] [table](#table) [sequential_entry](#sequential_entry) \{ [sequential_entry](#sequential_entry) } [endtable](#endtable)  
<a name="udp_initial_statement"></a>udp\_initial\_statement ::= [initial](#initial) [output_port_identifier](#output_port_identifier) `=` [init_val](#init_val) `;`  
<a name="init_val"></a>init\_val ::= [1](#1)`'`[b0](#b0) \| [1](#1)`'`[b1](#b1) \| [1](#1)`'`[bx](#bx) \| [1](#1)`'`[bX](#bX) \| [1](#1)`'`[B0](#B0) \| [1](#1)`'`[B1](#B1) \| [1](#1)`'`[Bx](#Bx) \| [1](#1)`'`[BX](#BX) \| [1](#1) \| [0](#0)  
<a name="sequential_entry"></a>sequential\_entry ::= [seq_input_list](#seq_input_list) `:` [current_state](#current_state) `:` [next_state](#next_state) `;`  
<a name="seq_input_list"></a>seq\_input\_list ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[level_input_list](#level_input_list)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [edge_input_list](#edge_input_list)  
<a name="level_input_list"></a>level\_input\_list ::= [level_symbol](#level_symbol) \{ [level_symbol](#level_symbol) }  
<a name="edge_input_list"></a>edge\_input\_list ::= \{ [level_symbol](#level_symbol) } [edge_indicator](#edge_indicator) \{ [level_symbol](#level_symbol) }  
<a name="edge_indicator"></a>edge\_indicator ::= `(` [level_symbol](#level_symbol) [level_symbol](#level_symbol) `)` \| [edge_symbol](#edge_symbol)  
<a name="current_state"></a>current\_state ::= [level_symbol](#level_symbol)  
<a name="next_state"></a>next\_state ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[output_symbol](#output_symbol)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `-`  
<a name="output_symbol"></a>output\_symbol ::= [0](#0) \| [1](#1) \| [x](#x) \| [X](#X)  
<a name="level_symbol"></a>level\_symbol ::= [0](#0) \| [1](#1) \| [x](#x) \| [X](#X) \| `?` \| [b](#b) \| [B](#B)  
<a name="edge_symbol"></a>edge\_symbol ::= [r](#r) \| [R](#R) \| [f](#f) \| [F](#F) \| [p](#p) \| [P](#P) \| [n](#n) \| [N](#N) \| `*`  
### A.5.4 UDP instantiation
<a name="udp_instantiation"></a>udp\_instantiation ::= [udp_identifier](#udp_identifier) \[ [drive_strength](#drive_strength) ] \[ [delay2](#delay2) ] [udp_instance](#udp_instance) \{ `,` [udp_instance](#udp_instance) } `;`  
<a name="udp_instance"></a>udp\_instance ::= \[ [name_of_instance](#name_of_instance) ] `(` [output_terminal](#output_terminal) `,` [input_terminal](#input_terminal) \{ `,` [input_terminal](#input_terminal) } `)`  
## A.6 Behavioral statements
### A.6.1 Continuous assignment and net alias statements
<a name="continuous_assign"></a>continuous\_assign ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assign](#assign) \[ [drive_strength](#drive_strength) ] \[ [delay3](#delay3) ] [list_of_net_assignments](#list_of_net_assignments) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assign](#assign) \[ [delay_control](#delay_control) ] [list_of_variable_assignments](#list_of_variable_assignments) `;`  
<a name="list_of_net_assignments"></a>list\_of\_net\_assignments ::= [net_assignment](#net_assignment) \{ `,` [net_assignment](#net_assignment) }  
<a name="list_of_variable_assignments"></a>list\_of\_variable\_assignments ::= [variable_assignment](#variable_assignment) \{ `,` [variable_assignment](#variable_assignment) }  
<a name="net_alias"></a>net\_alias ::= [alias](#alias) [net_lvalue](#net_lvalue) `=` [net_lvalue](#net_lvalue) \{ `=` [net_lvalue](#net_lvalue) } `;`  
<a name="net_assignment"></a>net\_assignment ::= [net_lvalue](#net_lvalue) `=` [expression](#expression)  
### A.6.2 Procedural blocks and assignments
<a name="initial_construct"></a>initial\_construct ::= [initial](#initial) [statement_or_null](#statement_or_null)  
<a name="always_construct"></a>always\_construct ::= [always_keyword](#always_keyword) [statement](#statement)  
<a name="always_keyword"></a>always\_keyword ::= [always](#always) \| [always_comb](#always_comb) \| [always_latch](#always_latch) \| [always_ff](#always_ff)  
<a name="final_construct"></a>final\_construct ::= [final](#final) [function_statement](#function_statement)  
<a name="blocking_assignment"></a>blocking\_assignment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[variable_lvalue](#variable_lvalue) `=` [delay_or_event_control](#delay_or_event_control) [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nonrange_variable_lvalue](#nonrange_variable_lvalue) `=` [dynamic_array_new](#dynamic_array_new)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [implicit_class_handle](#implicit_class_handle) `.` \| [class_scope](#class_scope) \| [package_scope](#package_scope) ] [hierarchical_variable_identifier](#hierarchical_variable_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;[select](#select) `=` [class_new](#class_new)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [operator_assignment](#operator_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inc_or_dec_expression](#inc_or_dec_expression)  
<a name="operator_assignment"></a>operator\_assignment ::= [variable_lvalue](#variable_lvalue) [assignment_operator](#assignment_operator) [expression](#expression)  
<a name="assignment_operator"></a>assignment\_operator ::= `=` \| `+=` \| `-=` \| `*=` \| `/=` \| `%=` \| `&=` \| `|=` \| `^=` \| `<<=` \| `>>=` \| `<<<=` \| `>>>=`  
<a name="nonblocking_assignment"></a>nonblocking\_assignment ::= [variable_lvalue](#variable_lvalue) `<=` \[ [delay_or_event_control](#delay_or_event_control) ] [expression](#expression)  
<a name="procedural_continuous_assignment"></a>procedural\_continuous\_assignment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assign](#assign)   [variable_assignment](#variable_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [deassign](#deassign) [variable_lvalue](#variable_lvalue)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [force](#force)    [variable_assignment](#variable_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [force](#force)       [net_assignment](#net_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [release](#release)   [variable_lvalue](#variable_lvalue)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [release](#release)   [net_lvalue](#net_lvalue)  
<a name="variable_assignment"></a>variable\_assignment ::= [variable_lvalue](#variable_lvalue) `=` [expression](#expression)  
### A.6.3 Parallel and sequential blocks
<a name="action_block"></a>action\_block ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [statement](#statement) ] [else](#else) [statement_or_null](#statement_or_null)  
<a name="seq_block"></a>seq\_block ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[begin](#begin) \[ `:` [block_identifier](#block_identifier) ] \{ [block_item_declaration](#block_item_declaration) } \{ [statement_or_null](#statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[end](#end) \[ `:` [block_identifier](#block_identifier) ]  
<a name="par_block"></a>par\_block ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[fork](#fork) \[ `:` [block_identifier](#block_identifier) ] \{ [block_item_declaration](#block_item_declaration) } \{ [statement_or_null](#statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;[join_keyword](#join_keyword) \[ `:` [block_identifier](#block_identifier) ]  
<a name="join_keyword"></a>join\_keyword ::= [join](#join) \| [join_any](#join_any) \| [join_none](#join_none)  
### A.6.4 Statements
<a name="statement_or_null"></a>statement\_or\_null ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[statement](#statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } `;`  
<a name="statement"></a>statement ::= \[ [block_identifier](#block_identifier) `:` ] \{ [attribute_instance](#attribute_instance) } [statement_item](#statement_item)  
<a name="statement_item"></a>statement\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[blocking_assignment](#blocking_assignment) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [nonblocking_assignment](#nonblocking_assignment) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [procedural_continuous_assignment](#procedural_continuous_assignment) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [case_statement](#case_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [conditional_statement](#conditional_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [subroutine_call_statement](#subroutine_call_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [disable_statement](#disable_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event_trigger](#event_trigger)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [loop_statement](#loop_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [jump_statement](#jump_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [par_block](#par_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [procedural_timing_control_statement](#procedural_timing_control_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [seq_block](#seq_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [wait_statement](#wait_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [procedural_assertion_statement](#procedural_assertion_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_drive](#clocking_drive) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [randsequence_statement](#randsequence_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [randcase_statement](#randcase_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expect_property_statement](#expect_property_statement)  
<a name="function_statement"></a>function\_statement ::= [statement](#statement)  
<a name="function_statement_or_null"></a>function\_statement\_or\_null ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[function_statement](#function_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } `;`  
### A.6.5 Timing control statements
<a name="procedural_timing_control_statement"></a>procedural\_timing\_control\_statement ::= [procedural_timing_control](#procedural_timing_control) [statement_or_null](#statement_or_null)  
<a name="delay_or_event_control"></a>delay\_or\_event\_control ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[delay_control](#delay_control)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event_control](#event_control)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [repeat](#repeat) `(` [expression](#expression) `)` [event_control](#event_control)  
<a name="delay_control"></a>delay\_control ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`#` [delay_value](#delay_value)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `#` `(` [mintypmax_expression](#mintypmax_expression) `)`  
<a name="event_control"></a>event\_control ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[clocking_event](#clocking_event)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `@` `*`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `@` `(` `*` `)`  
<a name="clocking_event"></a>clocking\_event ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`@` [ps_identifier](#ps_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `@` [hierarchical_identifier](#hierarchical_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `@` `(` [event_expression](#event_expression) `)`  
<a name="event_expression36"></a>event\_expression36 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [edge_identifier](#edge_identifier) ] [expression](#expression) \[ [iff](#iff) [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_instance](#sequence_instance) \[ [iff](#iff) [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event_expression](#event_expression) [or](#or) [event_expression](#event_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event_expression](#event_expression) `,` [event_expression](#event_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [event_expression](#event_expression) `)`  
<a name="procedural_timing_control"></a>procedural\_timing\_control ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[delay_control](#delay_control)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [event_control](#event_control)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cycle_delay](#cycle_delay)  
<a name="jump_statement"></a>jump\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[return](#return) \[ [expression](#expression) ] `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [break](#break) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [continue](#continue) `;`  
<a name="wait_statement"></a>wait\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[wait](#wait) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [wait](#wait) [fork](#fork) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [wait_order](#wait_order) `(` [hierarchical_identifier](#hierarchical_identifier) \{ `,` [hierarchical_identifier](#hierarchical_identifier) } `)` [action_block](#action_block)  
<a name="event_trigger"></a>event\_trigger ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`->` [hierarchical_event_identifier](#hierarchical_event_identifier) [nonrange_select](#nonrange_select) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `->>` \[ [delay_or_event_control](#delay_or_event_control) ] [hierarchical_event_identifier](#hierarchical_event_identifier) [nonrange_select](#nonrange_select) `;`  
<a name="disable_statement"></a>disable\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[disable](#disable) [hierarchical_task_identifier](#hierarchical_task_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [disable](#disable) [hierarchical_block_identifier](#hierarchical_block_identifier) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [disable](#disable) [fork](#fork) `;`  
### A.6.6 Conditional statements
<a name="conditional_statement"></a>conditional\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [unique_priority](#unique_priority) ] [if](#if) `(` [cond_predicate](#cond_predicate) `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [else](#else) [if](#if) `(` [cond_predicate](#cond_predicate) `)` [statement_or_null](#statement_or_null) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [else](#else) [statement_or_null](#statement_or_null) ]  
<a name="unique_priority"></a>unique\_priority ::= [unique](#unique) \| [unique0](#unique0) \| [priority](#priority)  
<a name="cond_predicate"></a>cond\_predicate ::= [expression_or_cond_pattern](#expression_or_cond_pattern) \{ `&&&` [expression_or_cond_pattern](#expression_or_cond_pattern) }  
<a name="expression_or_cond_pattern"></a>expression\_or\_cond\_pattern ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cond_pattern](#cond_pattern)  
<a name="cond_pattern"></a>cond\_pattern ::= [expression](#expression) [matches](#matches) [pattern](#pattern)  
### A.6.7 Case statements
<a name="case_statement"></a>case\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [unique_priority](#unique_priority) ] [case_keyword](#case_keyword) `(` [case_expression](#case_expression) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;[case_item](#case_item) \{ [case_item](#case_item) } [endcase](#endcase)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [unique_priority](#unique_priority) ] [case_keyword](#case_keyword) `(` [case_expression](#case_expression) `)` [matches](#matches)  
&nbsp;&nbsp;&nbsp;&nbsp;[case_pattern_item](#case_pattern_item) \{ [case_pattern_item](#case_pattern_item) } [endcase](#endcase)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [unique_priority](#unique_priority) ] [case](#case) `(` [case_expression](#case_expression) `)` [inside](#inside)  
&nbsp;&nbsp;&nbsp;&nbsp;[case_inside_item](#case_inside_item) \{ [case_inside_item](#case_inside_item) } [endcase](#endcase)  
<a name="case_keyword"></a>case\_keyword ::= [case](#case) \| [casez](#casez) \| [casex](#casex)  
<a name="case_expression"></a>case\_expression ::= [expression](#expression)  
<a name="case_item"></a>case\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[case_item_expression](#case_item_expression) \{ `,` [case_item_expression](#case_item_expression) } `:` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [statement_or_null](#statement_or_null)  
<a name="case_pattern_item"></a>case\_pattern\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[pattern](#pattern) \[ `&&&` [expression](#expression) ] `:` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [statement_or_null](#statement_or_null)  
<a name="case_inside_item"></a>case\_inside\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[range_list](#range_list) `:` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [statement_or_null](#statement_or_null)  
<a name="case_item_expression"></a>case\_item\_expression ::= [expression](#expression)  
<a name="randcase_statement"></a>randcase\_statement ::= [randcase](#randcase) [randcase_item](#randcase_item) \{ [randcase_item](#randcase_item) } [endcase](#endcase)  
<a name="randcase_item"></a>randcase\_item ::= [expression](#expression) `:` [statement_or_null](#statement_or_null)  
<a name="range_list"></a>range\_list ::= [value_range](#value_range) \{ `,` [value_range](#value_range) }  
<a name="value_range"></a>value\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [expression](#expression) `:` [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ `$` `:` [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [expression](#expression) `:` `$` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [expression](#expression) `+/-` [expression](#expression) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [expression](#expression) `+%-` [expression](#expression) ]  
#### A.6.7.1 Patterns
<a name="pattern"></a>pattern ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [pattern](#pattern) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [variable_identifier](#variable_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` `*`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [tagged](#tagged) [member_identifier](#member_identifier) \[ [pattern](#pattern) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| `'` \{ [pattern](#pattern) \{ `,` [pattern](#pattern) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `'` \{ [member_identifier](#member_identifier) `:` [pattern](#pattern) \{ `,` [member_identifier](#member_identifier) `:` [pattern](#pattern) } }  
<a name="assignment_pattern"></a>assignment\_pattern ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`'` \{ [expression](#expression) \{ `,` [expression](#expression) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `'` \{ [structure_pattern_key](#structure_pattern_key) `:` [expression](#expression) \{ `,` [structure_pattern_key](#structure_pattern_key) `:` [expression](#expression) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `'` \{ [array_pattern_key](#array_pattern_key) `:` [expression](#expression) \{ `,` [array_pattern_key](#array_pattern_key) `:` [expression](#expression) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `'` \{ [constant_expression](#constant_expression) \{ [expression](#expression) \{ `,` [expression](#expression) } } }  
<a name="structure_pattern_key"></a>structure\_pattern\_key ::= [member_identifier](#member_identifier) \| [assignment_pattern_key](#assignment_pattern_key)  
<a name="array_pattern_key"></a>array\_pattern\_key ::= [constant_expression](#constant_expression) \| [assignment_pattern_key](#assignment_pattern_key)  
<a name="assignment_pattern_key"></a>assignment\_pattern\_key ::= [simple_type](#simple_type) \| [default](#default)  
<a name="assignment_pattern_expression"></a>assignment\_pattern\_expression ::= \[ [assignment_pattern_expression_type](#assignment_pattern_expression_type) ] [assignment_pattern](#assignment_pattern)  
<a name="assignment_pattern_expression_type"></a>assignment\_pattern\_expression\_type ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ps_type_identifier](#ps_type_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_parameter_identifier](#ps_parameter_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [integer_atom_type](#integer_atom_type)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_reference](#type_reference)  
<a name="constant_assignment_pattern_expression"></a>constant\_assignment\_pattern\_expression ::= [assignment_pattern_expression37](#assignment_pattern_expression37)  
<a name="assignment_pattern_net_lvalue"></a>assignment\_pattern\_net\_lvalue ::= `'` \{ [net_lvalue](#net_lvalue) \{ `,` [net_lvalue](#net_lvalue) } }  
<a name="assignment_pattern_variable_lvalue"></a>assignment\_pattern\_variable\_lvalue ::= `'` \{ [variable_lvalue](#variable_lvalue) \{ `,` [variable_lvalue](#variable_lvalue) } }  
### A.6.8 Looping statements
<a name="loop_statement"></a>loop\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[forever](#forever) [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [repeat](#repeat) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [while](#while) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [for](#for) `(` \[ [for_initialization](#for_initialization) ] `;` \[ [expression](#expression) ] `;` \[ [for_step](#for_step) ] `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [do](#do) [statement_or_null](#statement_or_null) [while](#while) `(` [expression](#expression) `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [foreach](#foreach) `(` [ps_or_hierarchical_array_identifier](#ps_or_hierarchical_array_identifier) \[ [loop_variables](#loop_variables) ] `)` [statement](#statement)  
<a name="for_initialization"></a>for\_initialization ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[list_of_variable_assignments](#list_of_variable_assignments)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [for_variable_declaration](#for_variable_declaration) \{ `,` [for_variable_declaration](#for_variable_declaration) }  
<a name="for_variable_declaration"></a>for\_variable\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [var](#var) ] [data_type](#data_type) [variable_identifier](#variable_identifier) `=` [expression](#expression) \{ `,` [variable_identifier](#variable_identifier) `=` [expression](#expression) }[18](#18)  
<a name="for_step"></a>for\_step ::= [for_step_assignment](#for_step_assignment) \{ `,` [for_step_assignment](#for_step_assignment) }  
<a name="for_step_assignment"></a>for\_step\_assignment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[operator_assignment](#operator_assignment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inc_or_dec_expression](#inc_or_dec_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_subroutine_call](#function_subroutine_call)  
<a name="loop_variables"></a>loop\_variables ::= \[ [index_variable_identifier](#index_variable_identifier) ] \{ `,` \[ [index_variable_identifier](#index_variable_identifier) ] }  
### A.6.9 Subroutine call statements
<a name="subroutine_call_statement"></a>subroutine\_call\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[subroutine_call](#subroutine_call) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [void](#void) `'` `(` [function_subroutine_call](#function_subroutine_call) `)` `;`  
### A.6.10 Assertion statements
<a name="assertion_item"></a>assertion\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[concurrent_assertion_item](#concurrent_assertion_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [deferred_immediate_assertion_item](#deferred_immediate_assertion_item)  
<a name="deferred_immediate_assertion_item"></a>deferred\_immediate\_assertion\_item ::= \[ [block_identifier](#block_identifier) `:` ] [deferred_immediate_assertion_statement](#deferred_immediate_assertion_statement)  
<a name="procedural_assertion_statement"></a>procedural\_assertion\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[concurrent_assertion_statement](#concurrent_assertion_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [immediate_assertion_statement](#immediate_assertion_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [checker_instantiation](#checker_instantiation)  
<a name="immediate_assertion_statement"></a>immediate\_assertion\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[simple_immediate_assertion_statement](#simple_immediate_assertion_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [deferred_immediate_assertion_statement](#deferred_immediate_assertion_statement)  
<a name="simple_immediate_assertion_statement"></a>simple\_immediate\_assertion\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[simple_immediate_assert_statement](#simple_immediate_assert_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [simple_immediate_assume_statement](#simple_immediate_assume_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [simple_immediate_cover_statement](#simple_immediate_cover_statement)  
<a name="deferred_immediate_assertion_statement"></a>deferred\_immediate\_assertion\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[deferred_immediate_assert_statement](#deferred_immediate_assert_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [deferred_immediate_assume_statement](#deferred_immediate_assume_statement)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [deferred_immediate_cover_statement](#deferred_immediate_cover_statement)  
<a name="simple_immediate_assert_statement"></a>simple\_immediate\_assert\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assert](#assert) `(` [expression](#expression) `)` [action_block](#action_block)  
<a name="simple_immediate_assume_statement"></a>simple\_immediate\_assume\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assume](#assume) `(` [expression](#expression) `)` [action_block](#action_block)  
<a name="simple_immediate_cover_statement"></a>simple\_immediate\_cover\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover](#cover) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
<a name="deferred_immediate_assert_statement"></a>deferred\_immediate\_assert\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assert](#assert) `#`[0](#0) `(` [expression](#expression) `)` [action_block](#action_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assert](#assert) [final](#final) `(` [expression](#expression) `)` [action_block](#action_block)  
<a name="deferred_immediate_assume_statement"></a>deferred\_immediate\_assume\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[assume](#assume) `#`[0](#0) `(` [expression](#expression) `)` [action_block](#action_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assume](#assume) [final](#final) `(` [expression](#expression) `)` [action_block](#action_block)  
<a name="deferred_immediate_cover_statement"></a>deferred\_immediate\_cover\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[cover](#cover) `#`[0](#0) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cover](#cover) [final](#final) `(` [expression](#expression) `)` [statement_or_null](#statement_or_null)  
### A.6.11 Clocking block
<a name="clocking_declaration"></a>clocking\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [default](#default) ] [clocking](#clocking) \[ [clocking_identifier](#clocking_identifier) ] [clocking_event](#clocking_event) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [clocking_item](#clocking_item) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endclocking](#endclocking) \[ `:` [clocking_identifier](#clocking_identifier) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [global](#global) [clocking](#clocking) \[ [clocking_identifier](#clocking_identifier) ] [clocking_event](#clocking_event) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;[endclocking](#endclocking) \[ `:` [clocking_identifier](#clocking_identifier) ]  
<a name="clocking_item"></a>clocking\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[default](#default) [default_skew](#default_skew) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [clocking_direction](#clocking_direction) [list_of_clocking_decl_assign](#list_of_clocking_decl_assign) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [attribute_instance](#attribute_instance) } [assertion_item_declaration](#assertion_item_declaration)  
<a name="default_skew"></a>default\_skew ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[input](#input) [clocking_skew](#clocking_skew)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [output](#output) [clocking_skew](#clocking_skew)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [input](#input) [clocking_skew](#clocking_skew) [output](#output) [clocking_skew](#clocking_skew)  
<a name="clocking_direction"></a>clocking\_direction ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[input](#input) \[ [clocking_skew](#clocking_skew) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [output](#output) \[ [clocking_skew](#clocking_skew) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [input](#input) \[ [clocking_skew](#clocking_skew) ] [output](#output) \[ [clocking_skew](#clocking_skew) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inout](#inout)  
<a name="list_of_clocking_decl_assign"></a>list\_of\_clocking\_decl\_assign ::= [clocking_decl_assign](#clocking_decl_assign) \{ `,` [clocking_decl_assign](#clocking_decl_assign) }  
<a name="clocking_decl_assign"></a>clocking\_decl\_assign ::= [signal_identifier](#signal_identifier) \[ `=` [expression](#expression) ]  
<a name="clocking_skew"></a>clocking\_skew ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[edge_identifier](#edge_identifier) \[ [delay_control](#delay_control) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [delay_control](#delay_control)  
<a name="clocking_drive"></a>clocking\_drive ::= [clockvar_expression](#clockvar_expression) `<=` \[ [cycle_delay](#cycle_delay) ] [expression](#expression)  
<a name="cycle_delay"></a>cycle\_delay ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`##` [integral_number](#integral_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `##` [identifier](#identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `##` `(` [expression](#expression) `)`  
<a name="clockvar"></a>clockvar ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="clockvar_expression"></a>clockvar\_expression ::= [clockvar](#clockvar) [select](#select)  
### A.6.12 Randsequence
<a name="randsequence_statement"></a>randsequence\_statement ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[randsequence](#randsequence) `(` \[ [rs_production_identifier](#rs_production_identifier) ] `)`  
&nbsp;&nbsp;&nbsp;&nbsp;[rs_production](#rs_production) \{ [rs_production](#rs_production) }  
&nbsp;&nbsp;&nbsp;&nbsp;[endsequence](#endsequence)  
<a name="rs_production"></a>rs\_production ::= \[ [data_type_or_void](#data_type_or_void) ] [rs_production_identifier](#rs_production_identifier) \[ `(` [tf_port_list](#tf_port_list) `)` ] `:` [rs_rule](#rs_rule) \{ \| [rs_rule](#rs_rule) } `;`  
<a name="rs_rule"></a>rs\_rule ::= [rs_production_list](#rs_production_list) \[ `:=` [rs_weight_specification](#rs_weight_specification) \[ [rs_code_block](#rs_code_block) ] ]  
<a name="rs_production_list"></a>rs\_production\_list ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[rs_prod](#rs_prod) \{ [rs_prod](#rs_prod) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| [rand](#rand) [join](#join) \[ `(` [expression](#expression) `)` ] [rs_production_item](#rs_production_item) [rs_production_item](#rs_production_item) \{ [rs_production_item](#rs_production_item) }  
<a name="rs_weight_specification"></a>rs\_weight\_specification ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integral_number](#integral_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_identifier](#ps_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [expression](#expression) `)`  
<a name="rs_code_block"></a>rs\_code\_block ::= \{ \{ [data_declaration](#data_declaration) } \{ [statement_or_null](#statement_or_null) } }  
<a name="rs_prod"></a>rs\_prod ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[rs_production_item](#rs_production_item)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [rs_code_block](#rs_code_block)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [rs_if_else](#rs_if_else)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [rs_repeat](#rs_repeat)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [rs_case](#rs_case)  
<a name="rs_production_item"></a>rs\_production\_item ::= [rs_production_identifier](#rs_production_identifier) \[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
<a name="rs_if_else"></a>rs\_if\_else ::= [if](#if) `(` [expression](#expression) `)` [rs_production_item](#rs_production_item) \[ [else](#else) [rs_production_item](#rs_production_item) ]  
<a name="rs_repeat"></a>rs\_repeat ::= [repeat](#repeat) `(` [expression](#expression) `)` [rs_production_item](#rs_production_item)  
<a name="rs_case"></a>rs\_case ::= [case](#case) `(` [case_expression](#case_expression) `)` [rs_case_item](#rs_case_item) \{ [rs_case_item](#rs_case_item) } [endcase](#endcase)  
<a name="rs_case_item"></a>rs\_case\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[case_item_expression](#case_item_expression) \{ `,` [case_item_expression](#case_item_expression) } `:` [rs_production_item](#rs_production_item) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [default](#default) \[ `:` ] [rs_production_item](#rs_production_item) `;`  
## A.7 Specify section
### A.7.1 Specify block declaration
<a name="specify_block"></a>specify\_block ::= [specify](#specify) \{ [specify_item](#specify_item) } [endspecify](#endspecify)  
<a name="specify_item"></a>specify\_item ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[specparam_declaration](#specparam_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pulsestyle_declaration](#pulsestyle_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [showcancelled_declaration](#showcancelled_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [path_declaration](#path_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [system_timing_check](#system_timing_check)  
<a name="pulsestyle_declaration"></a>pulsestyle\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[pulsestyle_onevent](#pulsestyle_onevent) [list_of_path_outputs](#list_of_path_outputs) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [pulsestyle_ondetect](#pulsestyle_ondetect) [list_of_path_outputs](#list_of_path_outputs) `;`  
<a name="showcancelled_declaration"></a>showcancelled\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[showcancelled](#showcancelled) [list_of_path_outputs](#list_of_path_outputs) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [noshowcancelled](#noshowcancelled) [list_of_path_outputs](#list_of_path_outputs) `;`  
### A.7.2 Specify path declarations
<a name="path_declaration"></a>path\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[simple_path_declaration](#simple_path_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [edge_sensitive_path_declaration](#edge_sensitive_path_declaration) `;`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [state_dependent_path_declaration](#state_dependent_path_declaration) `;`  
<a name="simple_path_declaration"></a>simple\_path\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[parallel_path_description](#parallel_path_description) `=` [path_delay_value](#path_delay_value)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [full_path_description](#full_path_description) `=` [path_delay_value](#path_delay_value)  
<a name="parallel_path_description"></a>parallel\_path\_description ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [specify_input_terminal_descriptor](#specify_input_terminal_descriptor) \[ [polarity_operator](#polarity_operator) ] `=>` [specify_output_terminal_descriptor](#specify_output_terminal_descriptor) `)`  
<a name="full_path_description"></a>full\_path\_description ::= `(` [list_of_path_inputs](#list_of_path_inputs) \[ [polarity_operator](#polarity_operator) ] `*>` [list_of_path_outputs](#list_of_path_outputs) `)`  
<a name="edge_sensitive_path_declaration"></a>edge\_sensitive\_path\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[parallel_edge_sensitive_path_description](#parallel_edge_sensitive_path_description) `=` [path_delay_value](#path_delay_value)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [full_edge_sensitive_path_description](#full_edge_sensitive_path_description) `=` [path_delay_value](#path_delay_value)  
<a name="parallel_edge_sensitive_path_description"></a>parallel\_edge\_sensitive\_path\_description ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` \[ [edge_identifier](#edge_identifier) ] [specify_input_terminal_descriptor](#specify_input_terminal_descriptor) \[ [polarity_operator](#polarity_operator) ] `=>`  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [specify_output_terminal_descriptor](#specify_output_terminal_descriptor) \[ [polarity_operator](#polarity_operator) ] `:` [data_source_expression](#data_source_expression) `)` `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` \[ [edge_identifier](#edge_identifier) ] [specify_input_terminal_descriptor](#specify_input_terminal_descriptor) \[ [polarity_operator](#polarity_operator) ] `=>`  
&nbsp;&nbsp;&nbsp;&nbsp;[specify_output_terminal_descriptor](#specify_output_terminal_descriptor) `)`  
<a name="full_edge_sensitive_path_description"></a>full\_edge\_sensitive\_path\_description ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`(` \[ [edge_identifier](#edge_identifier) ] [list_of_path_inputs](#list_of_path_inputs) \[ [polarity_operator](#polarity_operator) ] `*>`  
&nbsp;&nbsp;&nbsp;&nbsp;`(` [list_of_path_outputs](#list_of_path_outputs) \[ [polarity_operator](#polarity_operator) ] `:` [data_source_expression](#data_source_expression) `)` `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` \[ [edge_identifier](#edge_identifier) ] [list_of_path_inputs](#list_of_path_inputs) \[ [polarity_operator](#polarity_operator) ] `*>`  
&nbsp;&nbsp;&nbsp;&nbsp;[list_of_path_outputs](#list_of_path_outputs) `)`  
<a name="state_dependent_path_declaration"></a>state\_dependent\_path\_declaration ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[if](#if) `(` [module_path_expression](#module_path_expression) `)` [simple_path_declaration](#simple_path_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [if](#if) `(` [module_path_expression](#module_path_expression) `)` [edge_sensitive_path_declaration](#edge_sensitive_path_declaration)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ifnone](#ifnone) [simple_path_declaration](#simple_path_declaration)  
<a name="data_source_expression"></a>data\_source\_expression ::= [expression](#expression)  
<a name="edge_identifier"></a>edge\_identifier ::= [posedge](#posedge) \| [negedge](#negedge) \| [edge](#edge)  
<a name="polarity_operator"></a>polarity\_operator ::= `+` \| `-`  
### A.7.3 Specify block terminals
<a name="list_of_path_inputs"></a>list\_of\_path\_inputs ::= [specify_input_terminal_descriptor](#specify_input_terminal_descriptor) \{ `,` [specify_input_terminal_descriptor](#specify_input_terminal_descriptor) }  
<a name="list_of_path_outputs"></a>list\_of\_path\_outputs ::= [specify_output_terminal_descriptor](#specify_output_terminal_descriptor) \{ `,` [specify_output_terminal_descriptor](#specify_output_terminal_descriptor) }  
<a name="specify_input_terminal_descriptor"></a>specify\_input\_terminal\_descriptor ::= [input_identifier](#input_identifier) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
<a name="specify_output_terminal_descriptor"></a>specify\_output\_terminal\_descriptor ::= [output_identifier](#output_identifier) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
<a name="input_identifier"></a>input\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[input_port_identifier](#input_port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inout_port_identifier](#inout_port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_identifier](#interface_identifier) `.` [port_identifier](#port_identifier)  
<a name="output_identifier"></a>output\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[output_port_identifier](#output_port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inout_port_identifier](#inout_port_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [interface_identifier](#interface_identifier) `.` [port_identifier](#port_identifier)  
### A.7.4 Specify path delays
<a name="path_delay_value"></a>path\_delay\_value ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[list_of_path_delay_expressions](#list_of_path_delay_expressions)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [list_of_path_delay_expressions](#list_of_path_delay_expressions) `)`  
<a name="list_of_path_delay_expressions"></a>list\_of\_path\_delay\_expressions ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[t_path_delay_expression](#t_path_delay_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [trise_path_delay_expression](#trise_path_delay_expression) `,` [tfall_path_delay_expression](#tfall_path_delay_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [trise_path_delay_expression](#trise_path_delay_expression) `,` [tfall_path_delay_expression](#tfall_path_delay_expression) `,` [tz_path_delay_expression](#tz_path_delay_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [t01_path_delay_expression](#t01_path_delay_expression) `,` [t10_path_delay_expression](#t10_path_delay_expression) `,` [t0z_path_delay_expression](#t0z_path_delay_expression) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[tz1_path_delay_expression](#tz1_path_delay_expression) `,` [t1z_path_delay_expression](#t1z_path_delay_expression) `,` [tz0_path_delay_expression](#tz0_path_delay_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [t01_path_delay_expression](#t01_path_delay_expression) `,` [t10_path_delay_expression](#t10_path_delay_expression) `,` [t0z_path_delay_expression](#t0z_path_delay_expression) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[tz1_path_delay_expression](#tz1_path_delay_expression) `,` [t1z_path_delay_expression](#t1z_path_delay_expression) `,` [tz0_path_delay_expression](#tz0_path_delay_expression) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[t0x_path_delay_expression](#t0x_path_delay_expression) `,` [tx1_path_delay_expression](#tx1_path_delay_expression) `,` [t1x_path_delay_expression](#t1x_path_delay_expression) `,`  
&nbsp;&nbsp;&nbsp;&nbsp;[tx0_path_delay_expression](#tx0_path_delay_expression) `,` [txz_path_delay_expression](#txz_path_delay_expression) `,` [tzx_path_delay_expression](#tzx_path_delay_expression)  
<a name="t_path_delay_expression"></a>t\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="trise_path_delay_expression"></a>trise\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tfall_path_delay_expression"></a>tfall\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tz_path_delay_expression"></a>tz\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t01_path_delay_expression"></a>t01\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t10_path_delay_expression"></a>t10\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t0z_path_delay_expression"></a>t0z\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tz1_path_delay_expression"></a>tz1\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t1z_path_delay_expression"></a>t1z\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tz0_path_delay_expression"></a>tz0\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t0x_path_delay_expression"></a>t0x\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tx1_path_delay_expression"></a>tx1\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="t1x_path_delay_expression"></a>t1x\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tx0_path_delay_expression"></a>tx0\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="txz_path_delay_expression"></a>txz\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="tzx_path_delay_expression"></a>tzx\_path\_delay\_expression ::= [path_delay_expression](#path_delay_expression)  
<a name="path_delay_expression"></a>path\_delay\_expression ::= [constant_mintypmax_expression](#constant_mintypmax_expression)  
### A.7.5 System timing checks
#### A.7.5.1 System timing check commands
<a name="system_timing_check"></a>system\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[setup_timing_check](#setup_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[hold_timing_check](#hold_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[setuphold_timing_check](#setuphold_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[recovery_timing_check](#recovery_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[removal_timing_check](#removal_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[recrem_timing_check](#recrem_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[skew_timing_check](#skew_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[timeskew_timing_check](#timeskew_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[fullskew_timing_check](#fullskew_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[period_timing_check](#period_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[width_timing_check](#width_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[nochange_timing_check](#nochange_timing_check)  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="setup_timing_check"></a>setup\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[setup](#setup) `(` [data_event](#data_event) `,` [reference_event](#reference_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="hold_timing_check"></a>hold\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[hold](#hold) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="setuphold_timing_check"></a>setuphold\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[setuphold](#setuphold) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) `,` [timing_check_limit](#timing_check_limit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [notifier](#notifier) ] \[ `,` \[ [timestamp_condition](#timestamp_condition) ] \[ `,` \[ [timecheck_condition](#timecheck_condition) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [delayed_reference](#delayed_reference) ] \[ `,` \[ [delayed_data](#delayed_data) ] ] ] ] ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="recovery_timing_check"></a>recovery\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[recovery](#recovery) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="removal_timing_check"></a>removal\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[removal](#removal) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="recrem_timing_check"></a>recrem\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[recrem](#recrem) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) `,` [timing_check_limit](#timing_check_limit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [notifier](#notifier) ] \[ `,` \[ [timestamp_condition](#timestamp_condition) ] \[ `,` \[ [timecheck_condition](#timecheck_condition) ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [delayed_reference](#delayed_reference) ] \[ `,` \[ [delayed_data](#delayed_data) ] ] ] ] ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="skew_timing_check"></a>skew\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[skew](#skew) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="timeskew_timing_check"></a>timeskew\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[timeskew](#timeskew) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [notifier](#notifier) ] \[ `,` \[ [event_based_flag](#event_based_flag) ] \[ `,` \[ [remain_active_flag](#remain_active_flag) ] ] ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="fullskew_timing_check"></a>fullskew\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[fullskew](#fullskew) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [timing_check_limit](#timing_check_limit) `,` [timing_check_limit](#timing_check_limit)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `,` \[ [notifier](#notifier) ] \[ `,` \[ [event_based_flag](#event_based_flag) ] \[ `,` \[ [remain_active_flag](#remain_active_flag) ] ] ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="period_timing_check"></a>period\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[period](#period) `(` [controlled_reference_event](#controlled_reference_event) `,` [timing_check_limit](#timing_check_limit) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="width_timing_check"></a>width\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[width](#width) `(` [controlled_reference_event](#controlled_reference_event) `,` [timing_check_limit](#timing_check_limit) `,` [threshold](#threshold) \[ `,` \[ [notifier](#notifier) ] ] `)` `;`  
&nbsp;&nbsp;&nbsp;&nbsp;`$`  
<a name="nochange_timing_check"></a>nochange\_timing\_check ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`$`[nochange](#nochange) `(` [reference_event](#reference_event) `,` [data_event](#data_event) `,` [start_edge_offset](#start_edge_offset) `,` [end_edge_offset](#end_edge_offset) \[ `,` \[ [notifier](#notifier) ] ] `);`  
#### A.7.5.2 System timing check command arguments
<a name="controlled_reference_event"></a>controlled\_reference\_event ::= [controlled_timing_check_event](#controlled_timing_check_event)  
<a name="data_event"></a>data\_event ::= [timing_check_event](#timing_check_event)  
<a name="delayed_data"></a>delayed\_data ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[terminal_identifier](#terminal_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [terminal_identifier](#terminal_identifier) \[ [constant_mintypmax_expression](#constant_mintypmax_expression) ]  
<a name="delayed_reference"></a>delayed\_reference ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[terminal_identifier](#terminal_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [terminal_identifier](#terminal_identifier) \[ [constant_mintypmax_expression](#constant_mintypmax_expression) ]  
<a name="end_edge_offset"></a>end\_edge\_offset ::= [mintypmax_expression](#mintypmax_expression)  
<a name="event_based_flag"></a>event\_based\_flag ::= [constant_expression](#constant_expression)  
<a name="notifier"></a>notifier ::= [variable_identifier](#variable_identifier)  
<a name="reference_event"></a>reference\_event ::= [timing_check_event](#timing_check_event)  
<a name="remain_active_flag"></a>remain\_active\_flag ::= [constant_mintypmax_expression](#constant_mintypmax_expression)  
<a name="timecheck_condition"></a>timecheck\_condition ::= [mintypmax_expression](#mintypmax_expression)  
<a name="timestamp_condition"></a>timestamp\_condition ::= [mintypmax_expression](#mintypmax_expression)  
<a name="start_edge_offset"></a>start\_edge\_offset ::= [mintypmax_expression](#mintypmax_expression)  
<a name="threshold"></a>threshold ::= [constant_expression](#constant_expression)  
<a name="timing_check_limit"></a>timing\_check\_limit ::= [expression](#expression)  
#### A.7.5.3 System timing check event definitions
<a name="timing_check_event"></a>timing\_check\_event ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [timing_check_event_control](#timing_check_event_control) ] [specify_terminal_descriptor](#specify_terminal_descriptor) \[ `&&&` [timing_check_condition](#timing_check_condition) ]  
<a name="controlled_timing_check_event"></a>controlled\_timing\_check\_event ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[timing_check_event_control](#timing_check_event_control) [specify_terminal_descriptor](#specify_terminal_descriptor) \[ `&&&` [timing_check_condition](#timing_check_condition) ]  
<a name="timing_check_event_control"></a>timing\_check\_event\_control ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[posedge](#posedge)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [negedge](#negedge)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [edge](#edge)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [edge_control_specifier](#edge_control_specifier)  
<a name="specify_terminal_descriptor"></a>specify\_terminal\_descriptor ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[specify_input_terminal_descriptor](#specify_input_terminal_descriptor)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [specify_output_terminal_descriptor](#specify_output_terminal_descriptor)  
<a name="edge_control_specifier"></a>edge\_control\_specifier ::= [edge](#edge) \[ [edge_descriptor](#edge_descriptor) \{ `,` [edge_descriptor](#edge_descriptor) } ]  
<a name="edge_descriptor38"></a>edge\_descriptor38 ::= [01](#01) \| [10](#10) \| [z_or_x](#z_or_x) [zero_or_one](#zero_or_one) \| [zero_or_one](#zero_or_one) [z_or_x](#z_or_x)  
<a name="zero_or_one"></a>zero\_or\_one ::= [0](#0) \| [1](#1)  
<a name="z_or_x"></a>z\_or\_x ::= [x](#x) \| [X](#X) \| [z](#z) \| [Z](#Z)  
<a name="timing_check_condition"></a>timing\_check\_condition ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[scalar_timing_check_condition](#scalar_timing_check_condition)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [scalar_timing_check_condition](#scalar_timing_check_condition) `)`  
<a name="scalar_timing_check_condition"></a>scalar\_timing\_check\_condition ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `~` [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `==` [scalar_constant](#scalar_constant)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `===` [scalar_constant](#scalar_constant)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `!=` [scalar_constant](#scalar_constant)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `!==` [scalar_constant](#scalar_constant)  
<a name="scalar_constant"></a>scalar\_constant ::= [1](#1)`'`[b0](#b0) \| [1](#1)`'`[b1](#b1) \| [1](#1)`'`[B0](#B0) \| [1](#1)`'`[B1](#B1) \| `'`[b0](#b0) \| `'`[b1](#b1) \| `'`[B0](#B0) \| `'`[B1](#B1) \| [1](#1) \| [0](#0)  
## A.8 Expressions
### A.8.1 Concatenations
<a name="concatenation"></a>concatenation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [expression](#expression) \{ `,` [expression](#expression) } }  
<a name="constant_concatenation"></a>constant\_concatenation ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\{ [constant_expression](#constant_expression) \{ `,` [constant_expression](#constant_expression) } }  
<a name="constant_multiple_concatenation"></a>constant\_multiple\_concatenation ::= \{ [constant_expression](#constant_expression) [constant_concatenation](#constant_concatenation) }  
<a name="module_path_concatenation"></a>module\_path\_concatenation ::= \{ [module_path_expression](#module_path_expression) \{ `,` [module_path_expression](#module_path_expression) } }  
<a name="module_path_multiple_concatenation"></a>module\_path\_multiple\_concatenation ::= \{ [constant_expression](#constant_expression) [module_path_concatenation](#module_path_concatenation) }  
<a name="multiple_concatenation"></a>multiple\_concatenation ::= \{ [expression](#expression) [concatenation](#concatenation) }[39](#39)  
<a name="streaming_concatenation"></a>streaming\_concatenation ::= \{ [stream_operator](#stream_operator) \[ [slice_size](#slice_size) ] [stream_concatenation](#stream_concatenation) }  
<a name="stream_operator"></a>stream\_operator ::= `>>` \| `<<`  
<a name="slice_size"></a>slice\_size ::= [simple_type](#simple_type) \| [constant_expression](#constant_expression)  
<a name="stream_concatenation"></a>stream\_concatenation ::= \{ [stream_expression](#stream_expression) \{ `,` [stream_expression](#stream_expression) } }  
<a name="stream_expression"></a>stream\_expression ::= [expression](#expression) \[ [with](#with) \[ [array_range_expression](#array_range_expression) ] ]  
<a name="array_range_expression"></a>array\_range\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `:` [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `+:` [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `-:` [expression](#expression)  
<a name="empty_unpacked_array_concatenation40"></a>empty\_unpacked\_array\_concatenation40 ::= \{ }  
### A.8.2 Subroutine calls
<a name="constant_function_call"></a>constant\_function\_call ::= [function_subroutine_call41](#function_subroutine_call41)  
<a name="tf_call42"></a>tf\_call42 ::= [ps_or_hierarchical_tf_identifier](#ps_or_hierarchical_tf_identifier) \{ [attribute_instance](#attribute_instance) } \[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
<a name="system_tf_call"></a>system\_tf\_call ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[system_tf_identifier](#system_tf_identifier) \[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [system_tf_identifier](#system_tf_identifier) `(` [data_type](#data_type) \[ `,` [expression](#expression) ] `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [system_tf_identifier](#system_tf_identifier) `(` [expression](#expression) \{ `,` \[ [expression](#expression) ] } \[ `,` \[ [clocking_event](#clocking_event) ] ] `)`  
<a name="subroutine_call"></a>subroutine\_call ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[tf_call](#tf_call)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [system_tf_call](#system_tf_call)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [method_call](#method_call)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [std](#std) `::` ] [randomize_call](#randomize_call)  
<a name="function_subroutine_call"></a>function\_subroutine\_call ::= [subroutine_call](#subroutine_call)  
<a name="list_of_arguments"></a>list\_of\_arguments ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [expression](#expression) ] \{ `,` \[ [expression](#expression) ] } \{ `,` `.` [identifier](#identifier) `(` \[ [expression](#expression) ] `)` }  
&nbsp;&nbsp;&nbsp;&nbsp;\| `.` [identifier](#identifier) `(` \[ [expression](#expression) ] `)` \{ `,` `.` [identifier](#identifier) `(` \[ [expression](#expression) ] `)` }  
<a name="method_call"></a>method\_call ::= [method_call_root](#method_call_root) `.` [method_call_body](#method_call_body)  
<a name="method_call_body"></a>method\_call\_body ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[method_identifier](#method_identifier) \{ [attribute_instance](#attribute_instance) } \[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [built_in_method_call](#built_in_method_call)  
<a name="built_in_method_call"></a>built\_in\_method\_call ::= [array_manipulation_call](#array_manipulation_call) \| [randomize_call](#randomize_call)  
<a name="array_manipulation_call"></a>array\_manipulation\_call ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[array_method_name](#array_method_name) \{ [attribute_instance](#attribute_instance) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `(` [list_of_arguments](#list_of_arguments) `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [with](#with) `(` [expression](#expression) `)` ]  
<a name="randomize_call"></a>randomize\_call ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[randomize](#randomize) \{ [attribute_instance](#attribute_instance) }  
&nbsp;&nbsp;&nbsp;&nbsp;\[ `(` \[ [variable_identifier_list](#variable_identifier_list) \| [null](#null) ] `)` ]  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [with](#with) \[ `(` \[ [identifier_list](#identifier_list) ] `)` ] [constraint_block](#constraint_block) ][43](#43)  
<a name="variable_identifier_list"></a>variable\_identifier\_list ::= [variable_identifier](#variable_identifier) \{ `,` [variable_identifier](#variable_identifier) }  
<a name="identifier_list"></a>identifier\_list ::= [identifier](#identifier) \{ `,` [identifier](#identifier) }  
<a name="method_call_root"></a>method\_call\_root ::= [primary](#primary) \| [implicit_class_handle](#implicit_class_handle)  
<a name="array_method_name"></a>array\_method\_name ::= [method_identifier](#method_identifier) \| [unique](#unique) \| [and](#and) \| [or](#or) \| [xor](#xor)  
### A.8.3 Expressions
<a name="inc_or_dec_expression"></a>inc\_or\_dec\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[inc_or_dec_operator](#inc_or_dec_operator) \{ [attribute_instance](#attribute_instance) } [variable_lvalue](#variable_lvalue)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [variable_lvalue](#variable_lvalue) \{ [attribute_instance](#attribute_instance) } [inc_or_dec_operator](#inc_or_dec_operator)  
<a name="conditional_expression"></a>conditional\_expression ::= [cond_predicate](#cond_predicate) `?` \{ [attribute_instance](#attribute_instance) } [expression](#expression) `:` [expression](#expression)  
<a name="constant_expression"></a>constant\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_primary](#constant_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unary_operator](#unary_operator) \{ [attribute_instance](#attribute_instance) } [constant_primary](#constant_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression) [binary_operator](#binary_operator) \{ [attribute_instance](#attribute_instance) } [constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression) `?` \{ [attribute_instance](#attribute_instance) } [constant_expression](#constant_expression) `:` [constant_expression](#constant_expression)  
<a name="constant_mintypmax_expression"></a>constant\_mintypmax\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression) `:` [constant_expression](#constant_expression) `:` [constant_expression](#constant_expression)  
<a name="constant_param_expression"></a>constant\_param\_expression ::= [constant_mintypmax_expression](#constant_mintypmax_expression) \| [data_type](#data_type) \| `$`  
<a name="param_expression"></a>param\_expression ::= [mintypmax_expression](#mintypmax_expression) \| [data_type](#data_type) \| `$`  
<a name="constant_range_expression"></a>constant\_range\_expression ::= [constant_expression](#constant_expression) \| [constant_part_select_range](#constant_part_select_range)  
<a name="constant_part_select_range"></a>constant\_part\_select\_range ::= [constant_range](#constant_range) \| [constant_indexed_range](#constant_indexed_range)  
<a name="constant_range"></a>constant\_range ::= [constant_expression](#constant_expression) `:` [constant_expression](#constant_expression)  
<a name="constant_indexed_range"></a>constant\_indexed\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[constant_expression](#constant_expression) `+:` [constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_expression](#constant_expression) `-:` [constant_expression](#constant_expression)  
<a name="expression"></a>expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[primary](#primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unary_operator](#unary_operator) \{ [attribute_instance](#attribute_instance) } [primary](#primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inc_or_dec_expression](#inc_or_dec_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [operator_assignment](#operator_assignment) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) [binary_operator](#binary_operator) \{ [attribute_instance](#attribute_instance) } [expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [conditional_expression](#conditional_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [inside_expression](#inside_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [tagged_union_expression](#tagged_union_expression)  
<a name="tagged_union_expression"></a>tagged\_union\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[tagged](#tagged) [member_identifier](#member_identifier) \[ [primary](#primary) ]  
<a name="inside_expression"></a>inside\_expression ::= [expression](#expression) [inside](#inside) \{ [range_list](#range_list) }  
<a name="mintypmax_expression"></a>mintypmax\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `:` [expression](#expression) `:` [expression](#expression)  
<a name="module_path_conditional_expression"></a>module\_path\_conditional\_expression ::= [module_path_expression](#module_path_expression) `?` \{ [attribute_instance](#attribute_instance) }  
&nbsp;&nbsp;&nbsp;&nbsp;[module_path_expression](#module_path_expression) `:` [module_path_expression](#module_path_expression)  
<a name="module_path_expression"></a>module\_path\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_path_primary](#module_path_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unary_module_path_operator](#unary_module_path_operator) \{ [attribute_instance](#attribute_instance) } [module_path_primary](#module_path_primary)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_path_expression](#module_path_expression) [binary_module_path_operator](#binary_module_path_operator) \{ [attribute_instance](#attribute_instance) }  
&nbsp;&nbsp;&nbsp;&nbsp;[module_path_expression](#module_path_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_path_conditional_expression](#module_path_conditional_expression)  
<a name="module_path_mintypmax_expression"></a>module\_path\_mintypmax\_expression ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[module_path_expression](#module_path_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_path_expression](#module_path_expression) `:` [module_path_expression](#module_path_expression) `:` [module_path_expression](#module_path_expression)  
<a name="part_select_range"></a>part\_select\_range ::= [constant_range](#constant_range) \| [indexed_range](#indexed_range)  
<a name="indexed_range"></a>indexed\_range ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[expression](#expression) `+:` [constant_expression](#constant_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [expression](#expression) `-:` [constant_expression](#constant_expression)  
<a name="genvar_expression"></a>genvar\_expression ::= [constant_expression](#constant_expression)  
### A.8.4 Primaries
<a name="constant_primary"></a>constant\_primary ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[primary_literal](#primary_literal)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [ps_parameter_identifier](#ps_parameter_identifier) [constant_select](#constant_select)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [specparam_identifier](#specparam_identifier) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [genvar_identifier44](#genvar_identifier44)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [formal_port_identifier](#formal_port_identifier) [constant_select](#constant_select)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [package_scope](#package_scope) \| [class_scope](#class_scope) ] [enum_identifier](#enum_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [empty_unpacked_array_concatenation](#empty_unpacked_array_concatenation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_concatenation](#constant_concatenation) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_multiple_concatenation](#constant_multiple_concatenation) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_function_call](#constant_function_call) \[ \[ [constant_range_expression](#constant_range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_let_expression](#constant_let_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [constant_mintypmax_expression](#constant_mintypmax_expression) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_cast](#constant_cast)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [constant_assignment_pattern_expression](#constant_assignment_pattern_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [type_reference45](#type_reference45)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [null](#null)  
<a name="module_path_primary"></a>module\_path\_primary ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[number](#number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [identifier](#identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_path_concatenation](#module_path_concatenation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [module_path_multiple_concatenation](#module_path_multiple_concatenation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_subroutine_call](#function_subroutine_call)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [module_path_mintypmax_expression](#module_path_mintypmax_expression) `)`  
<a name="primary"></a>primary ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[primary_literal](#primary_literal)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [class_qualifier](#class_qualifier) \| [package_scope](#package_scope) ] [hierarchical_identifier](#hierarchical_identifier) [select](#select)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [empty_unpacked_array_concatenation](#empty_unpacked_array_concatenation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [concatenation](#concatenation) \[ \[ [range_expression](#range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [multiple_concatenation](#multiple_concatenation) \[ \[ [range_expression](#range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [function_subroutine_call](#function_subroutine_call) \[ \[ [range_expression](#range_expression) ] ]  
&nbsp;&nbsp;&nbsp;&nbsp;\| [let_expression](#let_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `(` [mintypmax_expression](#mintypmax_expression) `)`  
&nbsp;&nbsp;&nbsp;&nbsp;\| [cast](#cast)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [assignment_pattern_expression](#assignment_pattern_expression)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [streaming_concatenation](#streaming_concatenation)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [sequence_method_call](#sequence_method_call)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [this46](#this46)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[47](#47)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [null](#null)  
&nbsp;&nbsp;&nbsp;&nbsp;[class_qualifier](#class_qualifier) `:=` \[ [local](#local) `::`[48](#48) ] \[ [implicit_class_handle](#implicit_class_handle) `.` \| [class_scope](#class_scope) ]  
<a name="range_expression"></a>range\_expression ::= [expression](#expression) \| [part_select_range](#part_select_range)  
<a name="primary_literal"></a>primary\_literal ::= [number](#number) \| [time_literal](#time_literal) \| [unbased_unsized_literal](#unbased_unsized_literal) \| [string_literal](#string_literal)  
<a name="time_literal49"></a>time\_literal49 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[unsigned_number](#unsigned_number) [time_unit](#time_unit)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [fixed_point_number](#fixed_point_number) [time_unit](#time_unit)  
<a name="time_unit"></a>time\_unit ::= [s](#s) \| [ms](#ms) \| [us](#us) \| [ns](#ns) \| [ps](#ps) \| [fs](#fs)  
<a name="implicit_class_handle46"></a>implicit\_class\_handle46 ::= [this](#this) \| [super](#super) \| [this](#this) `.` [super](#super)  
<a name="bit_select"></a>bit\_select ::= \{ \[ [expression](#expression) ] }  
<a name="select"></a>select ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ \{ `.` [member_identifier](#member_identifier) [bit_select](#bit_select) } `.` [member_identifier](#member_identifier) ] [bit_select](#bit_select) \[ \[ [part_select_range](#part_select_range) ] ]  
<a name="nonrange_select"></a>nonrange\_select ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ \{ `.` [member_identifier](#member_identifier) [bit_select](#bit_select) } `.` [member_identifier](#member_identifier) ] [bit_select](#bit_select)  
<a name="constant_bit_select"></a>constant\_bit\_select ::= \{ \[ [constant_expression](#constant_expression) ] }  
<a name="constant_select"></a>constant\_select ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ \{ `.` [member_identifier](#member_identifier) [constant_bit_select](#constant_bit_select) } `.` [member_identifier](#member_identifier) ] [constant_bit_select](#constant_bit_select)  
&nbsp;&nbsp;&nbsp;&nbsp;\[ \[ [constant_part_select_range](#constant_part_select_range) ] ]  
<a name="cast"></a>cast ::= [casting_type](#casting_type) `'` `(` [expression](#expression) `)`  
<a name="constant_cast"></a>constant\_cast ::= [casting_type](#casting_type) `'` `(` [constant_expression](#constant_expression) `)`  
<a name="constant_let_expression"></a>constant\_let\_expression ::= [let_expression50](#let_expression50)  
### A.8.5 Expression left-side values
<a name="net_lvalue"></a>net\_lvalue ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[ps_or_hierarchical_net_identifier](#ps_or_hierarchical_net_identifier) [constant_select](#constant_select)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [net_lvalue](#net_lvalue) \{ `,` [net_lvalue](#net_lvalue) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [assignment_pattern_expression_type](#assignment_pattern_expression_type) ] [assignment_pattern_net_lvalue](#assignment_pattern_net_lvalue)  
<a name="variable_lvalue"></a>variable\_lvalue ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [implicit_class_handle](#implicit_class_handle) `.`  \| [package_scope](#package_scope) ] [hierarchical_variable_identifier](#hierarchical_variable_identifier) [select51](#select51)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [variable_lvalue](#variable_lvalue) \{ `,` [variable_lvalue](#variable_lvalue) } }  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [assignment_pattern_expression_type](#assignment_pattern_expression_type) ] [assignment_pattern_variable_lvalue](#assignment_pattern_variable_lvalue)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [streaming_concatenation52](#streaming_concatenation52)  
<a name="nonrange_variable_lvalue"></a>nonrange\_variable\_lvalue ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [implicit_class_handle](#implicit_class_handle) `.` \| [package_scope](#package_scope) ] [hierarchical_variable_identifier](#hierarchical_variable_identifier) [nonrange_select](#nonrange_select)  
### A.8.6 Operators
<a name="unary_operator"></a>unary\_operator ::= `+` \| `-` \| `!` \| `~` \| `&` \| `~&` \| \| \| `~|` \| `^` \| `~^` \| `^~`  
<a name="binary_operator"></a>binary\_operator ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`+` \| `-` \| `*` \| `/` \| `%` \| `==` \| `!=` \| `===` \| `!==` \| `==?` \| `!=?` \| `&&` \| `||` \| `**`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `<` \| `<=` \| `>` \| `>=` \| `&` \| \| \| `^` \| `^~` \| `~^` \| `>>` \| `<<` \| `>>>` \| `<<<` `|->` \| `<->`  
<a name="inc_or_dec_operator"></a>inc\_or\_dec\_operator ::= `++` \| `--`  
<a name="unary_module_path_operator"></a>unary\_module\_path\_operator ::= `!` \| `~` \| `&` \| `~&` \| \| \| `~|` \| `^` \| `~^` \| `^~`  
<a name="binary_module_path_operator"></a>binary\_module\_path\_operator ::=  `==` \| `!=` \| `&&` \| `||` \| `&` \| \| \| `^` \| `^~` \| `~^`  
### A.8.7 Numbers
<a name="number"></a>number ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[integral_number](#integral_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [real_number](#real_number)  
<a name="integral_number"></a>integral\_number ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[decimal_number](#decimal_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [octal_number](#octal_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [binary_number](#binary_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hex_number](#hex_number)  
<a name="decimal_number"></a>decimal\_number ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[unsigned_number](#unsigned_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [size](#size) ] [decimal_base](#decimal_base) [unsigned_number](#unsigned_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [size](#size) ] [decimal_base](#decimal_base) [x_digit](#x_digit) \{ [_](#_) }  
&nbsp;&nbsp;&nbsp;&nbsp;\| \[ [size](#size) ] [decimal_base](#decimal_base) [z_digit](#z_digit) \{ [_](#_) }  
<a name="binary_number"></a>binary\_number ::= \[ [size](#size) ] [binary_base](#binary_base) [binary_value](#binary_value)  
<a name="octal_number"></a>octal\_number ::= \[ [size](#size) ] [octal_base](#octal_base) [octal_value](#octal_value)  
<a name="hex_number"></a>hex\_number ::= \[ [size](#size) ] [hex_base](#hex_base) [hex_value](#hex_value)  
<a name="sign"></a>sign ::= `+` \| `-`  
<a name="size"></a>size ::= [unsigned_number](#unsigned_number)  
<a name="real_number38"></a>real\_number38 ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[fixed_point_number](#fixed_point_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [unsigned_number](#unsigned_number) \[ `.` [unsigned_number](#unsigned_number) ] [exp](#exp) \[ [sign](#sign) ] [unsigned_number](#unsigned_number)  
<a name="fixed_point_number38"></a>fixed\_point\_number38 ::= [unsigned_number](#unsigned_number) `.` [unsigned_number](#unsigned_number)  
<a name="exp"></a>exp ::= [e](#e) \| [E](#E)  
<a name="unsigned_number38"></a>unsigned\_number38 ::= [decimal_digit](#decimal_digit) \{ [_](#_) \| [decimal_digit](#decimal_digit) }  
<a name="binary_value38"></a>binary\_value38 ::= [binary_digit](#binary_digit) \{ [_](#_) \| [binary_digit](#binary_digit) }  
<a name="octal_value38"></a>octal\_value38 ::= [octal_digit](#octal_digit) \{ [_](#_) \| [octal_digit](#octal_digit) }  
<a name="hex_value38"></a>hex\_value38 ::= [hex_digit](#hex_digit) \{ [_](#_) \| [hex_digit](#hex_digit) }  
<a name="decimal_base38"></a>decimal\_base38 ::= `'[`[s](#s)\|[S](#S)][d](#d) \| `'[`[s](#s)\|[S](#S)][D](#D)  
<a name="binary_base38"></a>binary\_base38 ::= `'[`[s](#s)\|[S](#S)][b](#b) \| `'[`[s](#s)\|[S](#S)][B](#B)  
<a name="octal_base38"></a>octal\_base38 ::= `'[`[s](#s)\|[S](#S)][o](#o) \| `'[`[s](#s)\|[S](#S)][O](#O)  
<a name="hex_base38"></a>hex\_base38 ::= `'[`[s](#s)\|[S](#S)][h](#h) \| `'[`[s](#s)\|[S](#S)][H](#H)  
<a name="decimal_digit"></a>decimal\_digit ::= [0](#0) \| [1](#1) \| [2](#2) \| [3](#3) \| [4](#4) \| [5](#5) \| [6](#6) \| [7](#7) \| [8](#8) \| [9](#9)  
<a name="binary_digit"></a>binary\_digit ::= [x_digit](#x_digit) \| [z_digit](#z_digit) \| [0](#0) \| [1](#1)  
<a name="octal_digit"></a>octal\_digit ::= [x_digit](#x_digit) \| [z_digit](#z_digit) \| [0](#0) \| [1](#1) \| [2](#2) \| [3](#3) \| [4](#4) \| [5](#5) \| [6](#6) \| [7](#7)  
<a name="hex_digit"></a>hex\_digit ::= [x_digit](#x_digit) \| [z_digit](#z_digit) \| [0](#0) \| [1](#1) \| [2](#2) \| [3](#3) \| [4](#4) \| [5](#5) \| [6](#6) \| [7](#7) \| [8](#8) \| [9](#9) \| [a](#a) \| [b](#b) \| [c](#c) \| [d](#d) \| [e](#e) \| [f](#f) \| [A](#A) \| [B](#B) \| [C](#C) \| [D](#D) \| [E](#E) \| [F](#F)  
<a name="x_digit"></a>x\_digit ::= [x](#x) \| [X](#X)  
<a name="z_digit"></a>z\_digit ::= [z](#z) \| [Z](#Z) \| `?`  
<a name="unbased_unsized_literal"></a>unbased\_unsized\_literal ::= `'`[0](#0) \| `'`[1](#1) \| `'`[z_or_x](#z_or_x) [53](#53)  
### A.8.8 Strings
<a name="string_literal"></a>string\_literal ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[quoted_string](#quoted_string)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [triple_quoted_string](#triple_quoted_string)  
<a name="quoted_string"></a>quoted\_string ::= `"` \{ [quoted_string_item](#quoted_string_item) \| [string_escape_seq](#string_escape_seq) } `"`  
<a name="triple_quoted_string"></a>triple\_quoted\_string ::= `"""` \{ [triple_quoted_string_item](#triple_quoted_string_item) \| [string_escape_seq](#string_escape_seq) } `"""`  
<a name="quoted_string_item"></a>quoted\_string\_item ::= [any_ASCII_character](#any_ASCII_character) [except](#except) `\` [or](#or) [newline](#newline) [or](#or) `"`  
<a name="triple_quoted_string_item"></a>triple\_quoted\_string\_item ::= [any_ASCII_character](#any_ASCII_character) [except](#except) `\`  
<a name="string_escape_seq"></a>string\_escape\_seq ::=  
&nbsp;&nbsp;&nbsp;&nbsp;`\`[any_ASCII_character](#any_ASCII_character)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `\`[one_to_three_digit_octal_number](#one_to_three_digit_octal_number)  
&nbsp;&nbsp;&nbsp;&nbsp;\| `\`[x](#x) [one_to_two_digit_hex_number](#one_to_two_digit_hex_number)  
## A.9 General
### A.9.1 Attributes
<a name="attribute_instance"></a>attribute\_instance ::= `(*` [attr_spec](#attr_spec) \{ `,` [attr_spec](#attr_spec) } `*)`  
<a name="attr_spec"></a>attr\_spec ::= [attr_name](#attr_name) \[ `=` [constant_expression](#constant_expression) ]  
<a name="attr_name"></a>attr\_name ::= [identifier](#identifier)  
### A.9.2 Comments
<a name="comment"></a>comment ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[one_line_comment](#one_line_comment)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [block_comment](#block_comment)  
<a name="one_line_comment"></a>one\_line\_comment ::= `//` [comment_text](#comment_text) `\`[n](#n)  
<a name="block_comment"></a>block\_comment ::= `/*` [comment_text](#comment_text) `*/`  
<a name="comment_text"></a>comment\_text ::= \{ [Any_ASCII_character](#Any_ASCII_character) }  
### A.9.3 Identifiers
<a name="array_identifier"></a>array\_identifier ::= [identifier](#identifier)  
<a name="block_identifier"></a>block\_identifier ::= [identifier](#identifier)  
<a name="bin_identifier"></a>bin\_identifier ::= [identifier](#identifier)  
<a name="c_identifier54"></a>c\_identifier54 ::= \[ [a](#a)`-`[zA](#zA)`-`[Z_](#Z_) ] \{ \[ [a](#a)`-`[zA](#zA)`-`[Z0](#Z0)`-`[9_](#9_) ] }  
<a name="cell_identifier"></a>cell\_identifier ::= [identifier](#identifier)  
<a name="checker_identifier"></a>checker\_identifier ::= [identifier](#identifier)  
<a name="class_identifier"></a>class\_identifier ::= [identifier](#identifier)  
<a name="class_variable_identifier"></a>class\_variable\_identifier ::= [variable_identifier](#variable_identifier)  
<a name="clocking_identifier"></a>clocking\_identifier ::= [identifier](#identifier)  
<a name="config_identifier"></a>config\_identifier ::= [identifier](#identifier)  
<a name="const_identifier"></a>const\_identifier ::= [identifier](#identifier)  
<a name="constraint_identifier"></a>constraint\_identifier ::= [identifier](#identifier)  
<a name="covergroup_identifier"></a>covergroup\_identifier ::= [identifier](#identifier)  
<a name="covergroup_variable_identifier"></a>covergroup\_variable\_identifier ::= [variable_identifier](#variable_identifier)  
<a name="cover_point_identifier"></a>cover\_point\_identifier ::= [identifier](#identifier)  
<a name="cross_identifier"></a>cross\_identifier ::= [identifier](#identifier)  
<a name="dynamic_array_variable_identifier"></a>dynamic\_array\_variable\_identifier ::= [variable_identifier](#variable_identifier)  
<a name="enum_identifier"></a>enum\_identifier ::= [identifier](#identifier)  
<a name="escaped_identifier"></a>escaped\_identifier ::= `\` \{ [any_printable_ASCII_character_except_white_space](#any_printable_ASCII_character_except_white_space) } [white_space](#white_space)  
<a name="formal_identifier"></a>formal\_identifier ::= [identifier](#identifier)  
<a name="formal_port_identifier"></a>formal\_port\_identifier ::= [identifier](#identifier)  
<a name="function_identifier"></a>function\_identifier ::= [identifier](#identifier)  
<a name="generate_block_identifier"></a>generate\_block\_identifier ::= [identifier](#identifier)  
<a name="genvar_identifier"></a>genvar\_identifier ::= [identifier](#identifier)  
<a name="hierarchical_array_identifier"></a>hierarchical\_array\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_block_identifier"></a>hierarchical\_block\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_event_identifier"></a>hierarchical\_event\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_identifier"></a>hierarchical\_identifier ::= \[ `$`[root](#root) `.` ] \{ [identifier](#identifier) [constant_bit_select](#constant_bit_select) `.` } [identifier](#identifier)  
<a name="hierarchical_net_identifier"></a>hierarchical\_net\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_parameter_identifier"></a>hierarchical\_parameter\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_property_identifier"></a>hierarchical\_property\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_sequence_identifier"></a>hierarchical\_sequence\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_task_identifier"></a>hierarchical\_task\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_tf_identifier"></a>hierarchical\_tf\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="hierarchical_variable_identifier"></a>hierarchical\_variable\_identifier ::= [hierarchical_identifier](#hierarchical_identifier)  
<a name="identifier"></a>identifier ::= [simple_identifier](#simple_identifier) \| [escaped_identifier](#escaped_identifier)  
<a name="index_variable_identifier"></a>index\_variable\_identifier ::= [identifier](#identifier)  
<a name="interface_identifier"></a>interface\_identifier ::= [identifier](#identifier)  
<a name="interface_port_identifier"></a>interface\_port\_identifier ::= [identifier](#identifier)  
<a name="inout_port_identifier"></a>inout\_port\_identifier ::= [identifier](#identifier)  
<a name="input_port_identifier"></a>input\_port\_identifier ::= [identifier](#identifier)  
<a name="instance_identifier"></a>instance\_identifier ::= [identifier](#identifier)  
<a name="library_identifier"></a>library\_identifier ::= [identifier](#identifier)  
<a name="member_identifier"></a>member\_identifier ::= [identifier](#identifier)  
<a name="method_identifier"></a>method\_identifier ::= [identifier](#identifier)  
<a name="modport_identifier"></a>modport\_identifier ::= [identifier](#identifier)  
<a name="module_identifier"></a>module\_identifier ::= [identifier](#identifier)  
<a name="net_identifier"></a>net\_identifier ::= [identifier](#identifier)  
<a name="nettype_identifier"></a>nettype\_identifier ::= [identifier](#identifier)  
<a name="output_port_identifier"></a>output\_port\_identifier ::= [identifier](#identifier)  
<a name="package_identifier"></a>package\_identifier ::= [identifier](#identifier)  
<a name="package_scope"></a>package\_scope ::=  
&nbsp;&nbsp;&nbsp;&nbsp;[package_identifier](#package_identifier) `::`  
&nbsp;&nbsp;&nbsp;&nbsp;\| `$`[unit](#unit) `::`  
<a name="parameter_identifier"></a>parameter\_identifier ::= [identifier](#identifier)  
<a name="port_identifier"></a>port\_identifier ::= [identifier](#identifier)  
<a name="program_identifier"></a>program\_identifier ::= [identifier](#identifier)  
<a name="property_identifier"></a>property\_identifier ::= [identifier](#identifier)  
<a name="ps_class_identifier"></a>ps\_class\_identifier ::= \[ [package_scope](#package_scope) ] [class_identifier](#class_identifier)  
<a name="ps_covergroup_identifier"></a>ps\_covergroup\_identifier ::= \[ [package_scope](#package_scope) ] [covergroup_identifier](#covergroup_identifier)  
<a name="ps_checker_identifier"></a>ps\_checker\_identifier ::= \[ [package_scope](#package_scope) ] [checker_identifier](#checker_identifier)  
<a name="ps_identifier"></a>ps\_identifier ::= \[ [package_scope](#package_scope) ] [identifier](#identifier)  
<a name="ps_or_hierarchical_array_identifier"></a>ps\_or\_hierarchical\_array\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [implicit_class_handle](#implicit_class_handle) `.` \| [class_scope](#class_scope) \| [package_scope](#package_scope) ] [hierarchical_array_identifier](#hierarchical_array_identifier)  
<a name="ps_or_hierarchical_net_identifier"></a>ps\_or\_hierarchical\_net\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [package_scope](#package_scope) ] [net_identifier](#net_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hierarchical_net_identifier](#hierarchical_net_identifier)  
<a name="ps_or_hierarchical_property_identifier"></a>ps\_or\_hierarchical\_property\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [package_scope](#package_scope) ] [property_identifier](#property_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hierarchical_property_identifier](#hierarchical_property_identifier)  
<a name="ps_or_hierarchical_sequence_identifier"></a>ps\_or\_hierarchical\_sequence\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [package_scope](#package_scope) ] [sequence_identifier](#sequence_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hierarchical_sequence_identifier](#hierarchical_sequence_identifier)  
<a name="ps_or_hierarchical_tf_identifier"></a>ps\_or\_hierarchical\_tf\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [package_scope](#package_scope) ] [tf_identifier](#tf_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| [hierarchical_tf_identifier](#hierarchical_tf_identifier)  
<a name="ps_parameter_identifier"></a>ps\_parameter\_identifier ::=  
&nbsp;&nbsp;&nbsp;&nbsp;\[ [package_scope](#package_scope) \| [class_scope](#class_scope) ] [parameter_identifier](#parameter_identifier)  
&nbsp;&nbsp;&nbsp;&nbsp;\| \{ [generate_block_identifier](#generate_block_identifier) \[ \[ [constant_expression](#constant_expression) ] ] `.` } [parameter_identifier](#parameter_identifier)  
<a name="ps_type_identifier"></a>ps\_type\_identifier ::= \[ [local](#local) `::`[48](#48) \| [package_scope](#package_scope) \| [class_scope](#class_scope) ] [type_identifier](#type_identifier)  
<a name="rs_production_identifier"></a>rs\_production\_identifier ::= [identifier](#identifier)  
<a name="sequence_identifier"></a>sequence\_identifier ::= [identifier](#identifier)  
<a name="signal_identifier"></a>signal\_identifier ::= [identifier](#identifier)  
<a name="simple_identifier54"></a>simple\_identifier54 ::= \[ [a](#a)`-`[zA](#zA)`-`[Z_](#Z_) ] \{ \[ [a](#a)`-`[zA](#zA)`-`[Z0](#Z0)`-`[9_](#9_)`$` ] }  
<a name="specparam_identifier"></a>specparam\_identifier ::= [identifier](#identifier)  
<a name="system_tf_identifier55"></a>system\_tf\_identifier55 ::= `$[` [a](#a)`-`[zA](#zA)`-`[Z0](#Z0)`-`[9_](#9_)`$` `]{` \[ [a](#a)`-`[zA](#zA)`-`[Z0](#Z0)`-`[9_](#9_)`$` ] }  
<a name="task_identifier"></a>task\_identifier ::= [identifier](#identifier)  
<a name="tf_identifier"></a>tf\_identifier ::= [identifier](#identifier)  
<a name="terminal_identifier"></a>terminal\_identifier ::= [identifier](#identifier)  
<a name="topmodule_identifier"></a>topmodule\_identifier ::= [identifier](#identifier)  
<a name="type_identifier"></a>type\_identifier ::= [identifier](#identifier)  
<a name="udp_identifier"></a>udp\_identifier ::= [identifier](#identifier)  
<a name="variable_identifier"></a>variable\_identifier ::= [identifier](#identifier)  
### A.9.4 White space
<a name="white_space"></a>white\_space ::= [space](#space) \| [tab](#tab) \| [newline](#newline) \| [formfeed](#formfeed) \| [eof56](#eof56)  
