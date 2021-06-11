<template>
    <div class="benchmark-list-pane" :class="{hidden: !show}">
        <ul class="benchmark-list">
            <li v-for="(files, dir) in data" :key="dir">
                <span class="benchmark-list-dirname">{{dir}}</span>
                <ul>
                    <template v-for="(input, fn) in files">
                        <li :key="fn" v-if="isBenchmark(fn)"
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
    padding-left: 1em;
}
ul.benchmark-list ul {
    padding-left: .8em;
}

ul.benchmark-list li {
    list-style: none;
}

ul.benchmark-list li::before {
    content: "\2023 ";
    width: .8em;
    margin-left: -.8em;
    display: inline-block;
}

ul.benchmark-list ul li::before {
    content: "\2022 ";
}
</style>

<script>
export default {
    data: () => ({data: {}, show: true}),
    methods: {
        isBenchmark(fn) { return fn.endsWith('.syn'); },
        select(a) {
            this.$emit('action', {type: 'select', ...a});
        }
    }
}
</script>
