#include <stdlib.h>
#include <stdio.h>
#include "options.h"

int main() {
    char* argv[] = {
        "",
        "-c",
        "free1",
        "--test",
        "-d", "51",
        "free2",
        "--test2=blah",
        "--test2="
    };
    int argc = 9;

    struct opt_list_t* list = create_opt_list();
    const opt_id_t OPT_C = insert_pattern(list, "c", NULL, false, NULL, "option c");
    const opt_id_t OPT_TEST = insert_pattern(list, "t", "test", false, NULL, "option test");
    const opt_id_t OPT_D = insert_pattern(list, "d", "test2", true, "foo", "option d");
    const opt_id_t OPT_X = insert_pattern(list, "x", "xx", true, "no", "option x");

    struct opt_parsed_t* parsed = parse_options(list, argc, argv);

    printf("error? %s\n", (has_error(parsed) ? "yes" : "no"));

    int nd = get_num_options(parsed, OPT_D);
    int nf = get_num_free_values(parsed);
    printf("num opt c: %d\n", get_num_options(parsed, OPT_C));
    printf("num opt test: %d\n", get_num_options(parsed, OPT_TEST));
    printf("num opt d: %d\n", nd);
    printf("num free values: %d\n", nf);

    char** opt_d = (char**)malloc(nd * sizeof(char*));
    get_option_values(parsed, OPT_D, opt_d);

    for (int i = 0; i < nd; i++) {
        printf("opt d [%d]: %s\n", i, opt_d[i]);
    }

    char** free_v = (char**)malloc(nf * sizeof(char*));
    get_free_values(parsed, free_v);

    for (int i = 0; i < nf; i++) {
        printf("free val [%d]: %s\n", i, free_v[i]);
    }

    printf("opt x: %s\n", get_option_value(parsed, OPT_X, 0));

    free(opt_d);
    free(free_v);

    destroy_opt_list(&list);
    dispose_options(&parsed);
    return 0;
}


