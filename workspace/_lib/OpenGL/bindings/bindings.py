import re

TYPE_MAP = {
    "void": "",

    "GLenum": "U32",
    "GLboolean": "U8",
    "GLbitfield": "U32",

    "GLbyte": "I8",
    "GLubyte": "U8",

    "GLshort": "I16",
    "GLushort": "U16",

    "GLint": "Int",
    "GLuint": "U32",

    "GLsizei": "Int",

    "GLfloat": "Float",
    "GLdouble": "F64",

    "GLchar": "U8",
    "GLintptr": "I64",
    "GLsizeiptr": "I64",

    "GLint64": "I64",
    "GLuint64": "U64",

    "GLsync": "VPtr",

    "GLint64EXT": "I64",
    "GLuint64EXT": "U64",
    "GLeglImageOES": "VPtr",

    "GLDEBUGPROC": "VPtr",
    "GLDEBUGPROCARB": "VPtr",
    "GLVULKANPROCNV": "VPtr",

    "struct _cl_context": "_none",
    "struct _cl_event": "_none"
}

prototype = re.compile(
    r'^GLAPI\s+(.+?)\s+APIENTRY\s+(\w+)\s*\((.*)\)\s*;'
)

def map_type(t, ptrNestFlag):
    t = t.strip()

    if t.startswith("const "):
        t = t[6:].strip()

    ptrs = t.count('*')
    t = t.replace('*', '').strip()

    if t not in TYPE_MAP:
        print(t)
        raise RuntimeError("Unknown OpenGL type")

    mapped = TYPE_MAP[t]
    if ptrs > 0:
        if mapped != "_none" and mapped != "":
            mapped = "CPtr[" + mapped + "]"
        else: 
            mapped = "VPtr"
    elif t == "_none":
        print(t)
        raise RuntimeError("Pointer-only OpenGL type used directly")

    if ptrNestFlag:
        if mapped == "":
            print(t)
            raise RuntimeError("Strange case nesting void inside const*")
        elif mapped != "VPtr":
            mapped = "CPtr[" + mapped + "]"

    return mapped


def split_parameter(param):
    """
    Split a C parameter declaration into (type, name),
    while normalizing pointer stars into the type.
    """

    param = param.strip()

    if param == "void":
        return ("void", "")

    pieces = param.rsplit(" ", 1)

    if len(pieces) == 1:
        ptype = pieces[0]
        pname = ""
    else:
        ptype, pname = pieces

    # Move pointer stars from the variable name into the type
    while pname.startswith("*"):
        ptype += " *"
        pname = pname[1:]

    # special common case
    ptrNestFlag = False
    if pname.startswith("const*"):
        pname = pname[6:]
        ptrNestFlag = True

    return (ptype.strip(), pname.strip(), ptrNestFlag)


with open("glcorearb.h") as f:
    for line in f:
        m = prototype.match(line)
        if not m:
            continue

        ret_type, name, params = m.groups()

        ret_type = map_type(ret_type, False)

        out_params = []

        params = params.strip()

        if params != "void":
            for p in params.split(","):
                p = p.strip()
                ptype, pname, pnf = split_parameter(p)

                ptype = map_type(ptype, pnf)

                out_params.append(f"{ptype} {pname}".strip())

        gladName = "glad_" + name
        print(f"fn {name}({', '.join(out_params)}) {ret_type} as " + gladName)