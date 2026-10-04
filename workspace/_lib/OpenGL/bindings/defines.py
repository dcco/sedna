import re

pattern = re.compile(r'^\s*#define\s+(GL_[A-Za-z0-9_]+)\s+(.+)$')

with open("glcorearb.h", "r") as f:
    for line in f:
        m = pattern.match(line)
        if not m:
            continue

        name, value = m.groups()
        name = name.upper()

        if not value.startswith("0x"):
            value = "_" + value

        # Ignore function-like macros
        if "(" in name:
            continue

        print(f"const _{name} = {value}")