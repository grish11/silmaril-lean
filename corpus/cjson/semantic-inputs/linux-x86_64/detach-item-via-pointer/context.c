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
__attribute__((visibility("default"))) cJSON * cJSON_DetachItemViaPointer(cJSON *parent, cJSON * const item)
{
    if ((parent == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (item == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                    ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                        ) || (item != parent->child && item->prev == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                                     ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                                         ))
    {
        return 
# 2247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if (item != parent->child)
    {

        item->prev->next = item->next;
    }
    if (item->next != 
# 2255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                     ((void *)0)
# 2255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         )
    {

        item->next->prev = item->prev;
    }

    if (item == parent->child)
    {

        parent->child = item->next;
    }
    else if (item->next == 
# 2266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 2266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              )
    {

        parent->child->prev = item->prev;
    }


    item->prev = 
# 2273 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2273 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    item->next = 
# 2274 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2274 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;

    return item;
}
