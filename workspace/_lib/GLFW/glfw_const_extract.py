import re

pattern = re.compile(r'^\s*#define\s+(GLFW_[A-Za-z0-9_]+)\s+(.+)$')

with open("glfw.h", "r") as f:
    for line in f:
        m = pattern.match(line)
        if not m:
            continue

        name, value = m.groups()

        if value.startswith("0x"):
            value = "+" + value

        # Ignore function-like macros
        if "(" in name:
            continue

        print(f"const _{name} = {value}")