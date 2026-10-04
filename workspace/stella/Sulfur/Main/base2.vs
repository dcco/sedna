#version 330
precision highp float;

layout (location = 0) in vec3 aPos;
layout (location = 1) in vec2 aTex;
layout (location = 2) in vec3 iPos;
layout (location = 3) in vec2 iSize;
layout (location = 4) in uint iColor;
layout (location = 5) in float iTexId;
layout (location = 6) in vec2 iUVPos;
layout (location = 7) in vec2 iUVSize;

uniform mat4 uPMat;
uniform int uTotal;
out vec2 vTex;
out float vTexId;
out vec3 vColor;

vec3 unpackRGB(uint c)
{
	float r = float((c >> 16) & 0xFFu) / 255.0;
	float g = float((c >> 8) & 0xFFu) / 255.0;
	float b = float(c & 0xFFu) / 255.0;
	return vec3(r, g, b);
}

void main(void) {
	vec2 pos = (aPos.xy * iSize) + iPos.xy;
	gl_Position = uPMat * vec4(pos, 0.0, 1.0);
	gl_Position.z = iPos.z;// / float(uTotal);
	vTex = (aTex * iUVSize) + iUVPos;
	vTexId = iTexId;
	vColor = unpackRGB(iColor);
}
