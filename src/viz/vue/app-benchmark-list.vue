<template>
    <ul>
        <li v-for="dir in data" :key="dir">{{dir}}</li>
    </ul>
</template>

<script>
export default {
    props: ['data']
}
</script>
