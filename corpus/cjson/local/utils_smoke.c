/* local/utils_smoke.c -- repository-authored test driver (not upstream). Why: exercises
 * libcjson_utils.so.1 (JSON Pointer, RFC 6902 patch generate/apply, RFC 7386 merge patch) together
 * with libcjson.so.1 in test.sh; it is not shipped as an artifact. Prints one line per check. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cJSON.h"
#include "cJSON_Utils.h"

static int fails;
static void expect(const char *what, const char *got, const char *want) {
    int ok = got && strcmp(got, want) == 0;
    printf("%s %s: %s\n", ok ? "ok" : "FAIL", what, got ? got : "(null)");
    if (!ok) fails++;
}

int main(void) {
    cJSON *a = cJSON_Parse("{\"name\":\"erebor\",\"tags\":[\"x\",\"y\"],\"n\":1}");
    cJSON *b = cJSON_Parse("{\"name\":\"erebor\",\"tags\":[\"x\",\"z\"],\"m\":2}");
    char *s;
    cJSON *p = cJSONUtils_GetPointer(a, "/tags/1");
    expect("GetPointer /tags/1", p ? p->valuestring : NULL, "y");
    cJSON *patch = cJSONUtils_GeneratePatches(a, b);
    s = cJSON_PrintUnformatted(patch);
    expect("GeneratePatches (cJSON sorts keys first)", s, "[{\"op\":\"add\",\"path\":\"/m\",\"value\":2},{\"op\":\"remove\",\"path\":\"/n\"},{\"op\":\"replace\",\"path\":\"/tags/1\",\"value\":\"z\"}]");
    free(s);
    cJSON *c = cJSON_Parse("{\"name\":\"erebor\",\"tags\":[\"x\",\"y\"],\"n\":1}");
    int rc = cJSONUtils_ApplyPatches(c, patch);
    cJSONUtils_SortObject(c); cJSONUtils_SortObject(b);
    printf("%s ApplyPatches rc=%d equal=%d\n", rc == 0 && cJSON_Compare(c, b, 1) ? "ok" : "FAIL", rc, cJSON_Compare(c, b, 1));
    if (!(rc == 0 && cJSON_Compare(c, b, 1))) fails++;
    cJSON *t = cJSON_Parse("{\"a\":\"b\",\"c\":{\"d\":\"e\",\"f\":\"g\"}}");
    cJSON *mp = cJSON_Parse("{\"a\":\"z\",\"c\":{\"f\":null}}");
    t = cJSONUtils_MergePatch(t, mp);
    s = cJSON_PrintUnformatted(t);
    expect("MergePatch (RFC 7386 example)", s, "{\"a\":\"z\",\"c\":{\"d\":\"e\"}}");
    free(s);
    cJSON_Delete(a); cJSON_Delete(b); cJSON_Delete(c); cJSON_Delete(patch); cJSON_Delete(t); cJSON_Delete(mp);
    printf("cJSON_Version %s\n", cJSON_Version());
    return fails != 0;
}
