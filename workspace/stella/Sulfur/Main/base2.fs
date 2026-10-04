#version 330
precision mediump float;
precision mediump sampler2DArray;

in vec2 vTex;
in float vTexId;
in vec3 vColor;

uniform sampler2DArray uSampler;
out vec4 FragColor;

void main(void) {
	vec4 texColor = texture(uSampler, vec3(vTex, vTexId));
	if (texColor.a == 0.0) discard;
	vec3 mColor = texColor.rgb * vColor.rgb;
	FragColor = vec4(mColor, texColor.a);
}