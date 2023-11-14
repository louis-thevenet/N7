#include <stdio.h>
#include <stdlib.h>
#include "viewport.h"

void show_area(const char* name, rect_t area) {
    printf("area %s: [%f,%f]×[%f,%f]\n",
            name,
            reelle(area.bottomleft), reelle(area.topright),
            imaginaire(area.bottomleft), imaginaire(area.topright));
}

void show_viewport(viewport_t viewport, SDL_Rect display) {
    printf("viewport: {%f x + %f, %f y + %f}\n",
            viewport.scale_x, viewport.off_x, viewport.scale_y, viewport.off_y);

    SDL_Rect d_unitrect;
    rect_t r_unitrect;

    from_display_rect(viewport, &r_unitrect, display);
    complexe_t taille;
    soustraire(&taille, r_unitrect.topright, r_unitrect.bottomleft);
    printf("- total screen area ([%d,%d]×[%d,%d]): [%f,%f]×[%f,%f] (size %f×%f)\n",
            display.x, display.x + display.w, 
            display.y, display.y + display.h,
            reelle(r_unitrect.bottomleft), reelle(r_unitrect.topright),
            imaginaire(r_unitrect.bottomleft), imaginaire(r_unitrect.topright),
            reelle(taille), imaginaire(taille));

    d_unitrect.x = 0;
    d_unitrect.y = 0;
    d_unitrect.w = 10;
    d_unitrect.h = 10;
    from_display_rect(viewport, &r_unitrect, d_unitrect);
    printf("- screen unit rect ([%d,%d]×[%d,%d]) transposed: [%f,%f]×[%f,%f]\n",
            d_unitrect.x, d_unitrect.x + d_unitrect.w, 
            d_unitrect.y, d_unitrect.y + d_unitrect.h,
            reelle(r_unitrect.bottomleft), reelle(r_unitrect.topright),
            imaginaire(r_unitrect.bottomleft), imaginaire(r_unitrect.topright));

    complexe_t c;
    init(&c, 0.0, 0.0);
    mkrect(&r_unitrect, c, 1.0, 1.0);
    from_real_rect(viewport, &d_unitrect, r_unitrect);
    printf("- real unit rect ([%f,%f]×[%f,%f]) transposed: [%d,%d]×[%d,%d]\n",
            reelle(r_unitrect.bottomleft), reelle(r_unitrect.topright),
            imaginaire(r_unitrect.bottomleft), imaginaire(r_unitrect.topright),
            d_unitrect.x, d_unitrect.x + d_unitrect.w, 
            d_unitrect.y, d_unitrect.y + d_unitrect.h);

    SDL_Point d_center;
    d_center.x = display.w / 2;
    d_center.y = display.h / 2;
    complexe_t r_center;
    from_display_point(viewport, &r_center, d_center);
    printf("- center (%d,%d): (%f,%f)\n",
            d_center.x, d_center.y,
            reelle(r_center), imaginaire(r_center));

}

int main() {
    SDL_Rect disp;
    complexe_t bl, center;
    rect_t rect, newarea;

    disp.x = 0;
    disp.y = 0;
    disp.w = 1500;
    disp.h = 1000;

    init(&bl, -7.5, -5.0);

    mkrect(&rect, bl, 15.0, 10.0);

    viewport_t vp1;
    viewport(&vp1, disp, rect);
    show_viewport(vp1, disp);

    puts("Scale by 0.5 (no translate)");
    init(&center, 0.0, 0.0);
    from_display_rect(vp1, &newarea, disp);
    scale_move_center(&newarea, 0.5, center);
    show_area("newarea", newarea);
    viewport(&vp1, disp, newarea);
    show_viewport(vp1, disp);

    puts("Scale by 0.5 + translate to new center (1.0, 1.0)");
    init(&center, 1.0, 1.0);
    from_display_rect(vp1, &newarea, disp);
    scale_move_center(&newarea, 0.5, center);
    show_area("newarea", newarea);
    viewport(&vp1, disp, newarea);
    show_viewport(vp1, disp);

    puts("Translate by (0.5,0.5)");
    init(&center, 0.5, 0.5);
    from_display_rect(vp1, &newarea, disp);
    translate_rect(&newarea, center);
    show_area("newarea", newarea);
    viewport(&vp1, disp, newarea);
    show_viewport(vp1, disp);

    return 0;
}


