typedef long unsigned int size_t;typedef struct cJSON
{

    struct cJSON *next;
    struct cJSON *prev;

    struct cJSON *child;


    int type;


    char *valuestring;

    int valueint;

    double valuedouble;


    char *string;
} cJSON;typedef int cJSON_bool;
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
static void suffix_object(cJSON *prev, cJSON *item)
{
    prev->next = item;
    item->prev = prev;
}
static cJSON_bool add_item_to_array(cJSON *array, cJSON *item)
{
    cJSON *child = 
# 2014 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2014 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;

    if ((item == 
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ) || (array == 
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ) || (array == item))
    {
        return ((cJSON_bool)0);
    }

    child = array->child;



    if (child == 
# 2025 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2025 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {

        array->child = item;
        item->prev = item;
        item->next = 
# 2030 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                    ((void *)0)
# 2030 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        ;
    }
    else
    {

        if (child->prev)
        {
            suffix_object(child->prev, item);
            array->child->prev = item;
        }
    }

    return ((cJSON_bool)1);
}
__attribute__((visibility("default"))) cJSON_bool cJSON_InsertItemInArray(cJSON *array, int which, cJSON *newitem)
{
    cJSON *after_inserted = 
# 2321 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 2321 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;

    if (which < 0 || newitem == 
# 2323 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                               ((void *)0)
# 2323 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   )
    {
        return ((cJSON_bool)0);
    }

    after_inserted = get_array_item(array, (size_t)which);
    if (after_inserted == 
# 2329 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 2329 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return add_item_to_array(array, newitem);
    }

    if (after_inserted != array->child && after_inserted->prev == 
# 2334 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                 ((void *)0)
# 2334 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                     ) {

        return ((cJSON_bool)0);
    }

    newitem->next = after_inserted;
    newitem->prev = after_inserted->prev;
    after_inserted->prev = newitem;
    if (after_inserted == array->child)
    {
        array->child = newitem;
    }
    else
    {
        newitem->prev->next = newitem;
    }
    return ((cJSON_bool)1);
}
