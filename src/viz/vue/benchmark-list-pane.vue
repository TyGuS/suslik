<template>
    <div class="ide-pane benchmark-list-pane" :class="{hidden: !show}">
        <ul class="benchmark-list">
            <li v-for="(files, dir) in data" :key="dir">
                <span class="benchmark-list-dirname">{{dir}}</span>
                <ul>
                    <template v-for="(input, fn) in files">
                        <li :key="fn" v-if="isBenchmark(fn)"
                            :class="{selected: isSelected({dir, fn})}"
                            @click="select({dir, fn})">{{fn}}</li>
                    </template>
                </ul>
            </li>
        </ul>
    </div>
</template>

<style>
.benchmark-list-pane.hidden {
    display: none;
}

ul.benchmark-list {
    padding-left: .2em;
    white-space: nowrap;
    text-overflow: ellipsis;
    font-family:  'Trebuchet MS', 'Lucida Sans Unicode', 'Lucida Grande', 'Lucida Sans', Arial, sans-serif;
    font-size: 12px;
    line-height: 1.2;
    cursor: pointer;
}
ul.benchmark-list ul {
    padding-left: 0;
}

ul.benchmark-list > li {
    margin-top: .3em;
    padding-left: .8em !important;
    margin-left: 0 !important;
    color: gray !important;
}

ul.benchmark-list li {
    list-style: none;
    overflow: hidden;
    color: black;
    text-overflow: ellipsis;
    padding-left: .5em;
    margin-left: -.5em;
}

ul.benchmark-list li::before {
    content: "\2023 ";
    font-family: times;
    width: .8em;
    margin-left: -.8em;
    display: inline-block;
}

ul.benchmark-list ul li::before {
    content: "";
}

ul.benchmark-list li.selected {
    background: blue;
    color: white;
}
</style>

<script>
export default {
    props: ['selected'],
    data: () => ({data: {}, show: true}),
    methods: {
        isBenchmark(fn) { return fn.match(/\.(sus|syn)$/); },
        select(a) {
            this.$emit('action', {type: 'select', ...a});
        },
        isSelected(entry /* {dir: string, fn: string} */) {
            return this.selected && 
                this.selected.dir === entry.dir && this.selected.fn === entry.fn;
        }
    }
}
</script>
