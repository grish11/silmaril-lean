typedef long unsigned int size_t;
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
static cJSON* get_array_item(const cJSON *array, size_t index)
{
    cJSON *current_child = 
# 1909 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 1909 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              ;

    if (array == 
# 1911 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1911 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        return 
# 1913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    current_child = array->child;
    while ((current_child != 
# 1917 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 1917 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                ) && (index > 0))
    {
        index--;
        current_child = current_child->next;
    }

    return current_child;
}

__attribute__((visibility("default"))) cJSON * cJSON_GetArrayItem(const cJSON *array, int index)
{
    if (index < 0)
    {
        return 
# 1930 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1930 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return get_array_item(array, (size_t)index);
}
