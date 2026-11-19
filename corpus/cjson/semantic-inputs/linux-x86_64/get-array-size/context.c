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
__attribute__((visibility("default"))) int cJSON_GetArraySize(const cJSON *array)
{
    cJSON *child = 
# 1886 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1886 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
    size_t size = 0;

    if (array == 
# 1889 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1889 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        return 0;
    }

    child = array->child;

    while(child != 
# 1896 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1896 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      )
    {
        size++;
        child = child->next;
    }



    return (int)size;
}
