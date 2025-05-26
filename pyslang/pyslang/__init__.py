# Import Pybind11 bindings
import json

from _pyslang import *


# Generic conversion from node to dict
def node_to_dict(node):
    if isinstance(node, (int, float, bool, str)):
        return node

    if node is None:
        return None

    cls_name = type(node).__name__

    if isinstance(node, (SyntaxKind, TokenKind, TriviaKind)):
        return str(node).split(".")[-1]

    if isinstance(node, SourceLocation):
        return {
            "type": cls_name,
            # "buffer": node.buffer, # TODO: Figure out how to serialize buffer
            "offset": node.offset,
        }

    if isinstance(node, list):
        return [node_to_dict(item) for item in node]

    if isinstance(node, dict):
        return {k: node_to_dict(v) for k, v in node.items()}

    text = str(node) if hasattr(node, "__str__") else None

    def custom_sort_key(item):
        # Put start before end, and sort others by name
        priority = {"kind": -100, "start": 0, "end": 1}
        return (priority.get(item, 20000), item)  # Secondary sort by name

    # Collect non-callable, non-private, non-cyclic attributes.
    exclude_fields = {"children", "parent", "child", "parents"}
    properties = {
        k: node_to_dict(getattr(node, k))
        for k in sorted(dir(node), key=custom_sort_key)
        if not k.startswith("_")
        and not callable(getattr(node, k))
        and k not in exclude_fields
    }

    result = {"type": cls_name, **properties}

    if text and not text.startswith("<") and not text.endswith(">"):
        result["text"] = text

    # Handle iterable children for SyntaxNode-like objects
    if hasattr(node, "__iter__"):
        result["children"] = [node_to_dict(child) for child in node]

    return result


# Extend relevant classes with `to_dict` and `to_json`
def _extend_with_serialization(cls):
    def to_dict(self):
        return node_to_dict(self)

    def to_json(self, **kwargs):
        return json.dumps(self.to_dict(), indent=2, **kwargs)

    cls.to_dict = to_dict
    cls.to_json = to_json


# Automatically register serialization for known node types
for cls in [SyntaxNode, Token, Trivia]:
    _extend_with_serialization(cls)
