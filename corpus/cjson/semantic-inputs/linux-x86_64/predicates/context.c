typedef struct cJSON
{

    struct cJSON *next;
    struct cJSON *prev;

    struct cJSON *child;


    int type;


    char *valuestring;

    int valueint;

    double valuedouble;


    char *string;
} cJSON;
typedef int cJSON_bool;
__attribute__((visibility("default"))) cJSON_bool cJSON_IsNull(const cJSON * const item)
{
    if (item == 
# 2999 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2999 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 2);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsBool(const cJSON * const item)
{
    if (item == 
# 2990 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2990 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & ((1 << 1) | (1 << 0))) != 0;
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsNumber(const cJSON * const item)
{
    if (item == 
# 3009 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3009 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 3);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsString(const cJSON * const item)
{
    if (item == 
# 3019 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3019 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 4);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsArray(const cJSON * const item)
{
    if (item == 
# 3029 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3029 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 5);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsObject(const cJSON * const item)
{
    if (item == 
# 3039 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3039 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 6);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsInvalid(const cJSON * const item)
{
    if (item == 
# 2959 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2959 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (0);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsFalse(const cJSON * const item)
{
    if (item == 
# 2969 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2969 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 0);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsTrue(const cJSON * const item)
{
    if (item == 
# 2979 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2979 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xff) == (1 << 1);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsRaw(const cJSON * const item)
{
    if (item == 
# 3049 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3049 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 7);
}
